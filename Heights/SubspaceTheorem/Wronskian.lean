module

public import Heights.SubspaceTheorem.GeneralizedWronskian

/-!
# Generalized Wronskians and heights of divided derivatives

Auxiliary results for the proof of Roth's lemma (`Schmidt.roth_lemma`, file `RothLemma`),
following [schmidt1980], Chapter V:

* `Schmidt.height_hasseDeriv_le`: heights of divided derivatives (Lemma 5A);
* `Schmidt.exists_tensor_decomposition`: the decomposition (10.8) with `k` minimal;
* `Schmidt.exists_wronskian_ne_zero` (file `GeneralizedWronskian`): generalized Wronskians
  (Lemma 9A);
* `Schmidt.exists_wronskian`: the Wronskian `W = V U` of the proof of Theorem 10A (p. 144);
* `Schmidt.exists_int_factorization`, `Schmidt.height_det_hasseDeriv_le`: integrality and heights
  of the factors (p. 145).
-/

@[expose] public section

namespace Schmidt

open MvPolynomial

/-! ### Divided derivatives -/

section Hasse

variable {σ R : Type*} [CommSemiring R]

/-- The divided derivative commutes with a change of coefficients. -/
lemma map_hasseDeriv {R' : Type*} [CommSemiring R'] (f : R →+* R') (i : σ →₀ ℕ)
    (P : MvPolynomial σ R) : map f (hasseDeriv i P) = hasseDeriv i (map f P) := by
  ext k
  rw [coeff_map, coeff_hasseDeriv, coeff_hasseDeriv, coeff_map, map_nsmul]

/-- Divided derivatives in disjoint sets of variables compose. -/
lemma hasseDeriv_hasseDeriv_of_disjoint [Fintype σ] {i j : σ →₀ ℕ}
    (h : ∀ v, i v = 0 ∨ j v = 0) (P : MvPolynomial σ R) :
    hasseDeriv j (hasseDeriv i P) = hasseDeriv (i + j) P := by
  rw [hasseDeriv_hasseDeriv, Finset.prod_eq_one (fun v _ ↦ by
    rcases h v with h | h <;> simp [h]), Nat.cast_one, map_one, one_mul]

lemma hasseDeriv_zero_right {σ R : Type*} [CommSemiring R] (i : σ →₀ ℕ) :
    hasseDeriv i (0 : MvPolynomial σ R) = 0 := by
  simp [hasseDeriv]

end Hasse


/-! ### Heights -/

section HeightLemmas

variable {σ : Type*}

lemma natAbs_coeff_le_height (P : MvPolynomial σ ℤ) (e : σ →₀ ℕ) :
    (P.coeff e).natAbs ≤ height P := by
  classical
  by_cases he : e ∈ P.support
  · exact Finset.le_sup (f := fun j ↦ (P.coeff j).natAbs) he
  · rw [notMem_support_iff.mp he]
    simp

lemma height_le_iff (P : MvPolynomial σ ℤ) (B : ℕ) :
    height P ≤ B ↔ ∀ e, (P.coeff e).natAbs ≤ B :=
  ⟨fun h e ↦ (natAbs_coeff_le_height P e).trans h, fun h ↦ Finset.sup_le fun e _ ↦ h e⟩

lemma height_add_le (A B : MvPolynomial σ ℤ) : height (A + B) ≤ height A + height B := by
  rw [height_le_iff]
  intro e
  have : (A + B).coeff e = A.coeff e + B.coeff e := by simp
  rw [this]
  exact (Int.natAbs_add_le _ _).trans
    (add_le_add (natAbs_coeff_le_height A e) (natAbs_coeff_le_height B e))

lemma height_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    height (∑ i ∈ s, f i) ≤ ∑ i ∈ s, height (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [height]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (height_add_le _ _).trans (Nat.add_le_add_left ih _)

lemma height_units_smul (u : ℤˣ) (A : MvPolynomial σ ℤ) : height (u • A) = height A := by
  classical
  unfold height
  rw [Units.smul_def, support_smul_eq (Units.ne_zero u)]
  refine Finset.sup_congr rfl fun e _ ↦ ?_
  rw [coeff_smul, smul_eq_mul, Int.natAbs_mul, Int.isUnit_iff_natAbs_eq.mp u.isUnit, one_mul]

lemma height_mul_le (A B : MvPolynomial σ ℤ) :
    height (A * B) ≤ A.support.card * height A * height B := by
  classical
  rw [height_le_iff]
  intro e
  have h1 : (A * B).coeff e =
      ∑ a ∈ A.support, (if a ≤ e then A.coeff a * B.coeff (e - a) else 0) := by
    conv_lhs => rw [A.as_sum, Finset.sum_mul, coeff_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [coeff_monomial_mul']
  rw [h1]
  calc (∑ a ∈ A.support, (if a ≤ e then A.coeff a * B.coeff (e - a) else 0)).natAbs
      ≤ ∑ a ∈ A.support, (if a ≤ e then A.coeff a * B.coeff (e - a) else 0).natAbs :=
        Int.natAbs_sum_le _ _
    _ ≤ ∑ _a ∈ A.support, height A * height B := by
        refine Finset.sum_le_sum fun a _ ↦ ?_
        split_ifs
        · rw [Int.natAbs_mul]
          exact Nat.mul_le_mul (natAbs_coeff_le_height A a) (natAbs_coeff_le_height B _)
        · simp
    _ = A.support.card * height A * height B := by
        rw [Finset.sum_const, smul_eq_mul, mul_assoc]

lemma height_one : height (1 : MvPolynomial σ ℤ) = 1 := by
  classical
  unfold height
  rw [support_one]
  simp

lemma height_prod_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    height (∏ i ∈ s, f i) ≤ ∏ i ∈ s, ((f i).support.card * height (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [height_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (height_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

variable [Fintype σ]

lemma card_support_le (P : MvPolynomial σ ℤ) (r : σ → ℕ) (hP : ∀ h, P.degreeOf h ≤ r h) :
    P.support.card ≤ 2 ^ (∑ h, r h) := by
  classical
  have h1 : P.support.card ≤ (Fintype.piFinset fun h ↦ Finset.range (r h + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun j ↦ ⇑j) (fun j hj ↦ ?_)
      (fun _ _ _ _ h ↦ DFunLike.coe_injective h)
    refine Fintype.mem_piFinset.mpr fun h ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
    exact (monomial_le_degreeOf h hj).trans (hP h)
  refine h1.trans ?_
  rw [Fintype.card_piFinset, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod fun h _ ↦ by
    rw [Finset.card_range]
    exact Nat.lt_two_pow_self

omit [Fintype σ] in
lemma degreeOf_hasseDeriv_le (P : MvPolynomial σ ℤ) (j : σ →₀ ℕ) (h : σ) :
    (hasseDeriv j P).degreeOf h ≤ P.degreeOf h := by
  rw [degreeOf_le_iff]
  intro k hk
  rw [mem_support_iff, coeff_hasseDeriv] at hk
  have h1 : P.coeff (k + j) ≠ 0 := fun h0 ↦ hk (by rw [h0, smul_zero])
  have := monomial_le_degreeOf h (mem_support_iff.mpr h1)
  simp only [Finsupp.add_apply] at this
  omega

end HeightLemmas

/-- [schmidt1980], Chapter V, Lemma 5A: if `P` has degree at most `r_h` in `X_h`, then
`|P_j| ≤ 2 ^ (r₁ + ⋯ + rₘ) |P|`. -/
lemma height_hasseDeriv_le {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℤ) (r : σ → ℕ)
    (hP : ∀ h, P.degreeOf h ≤ r h) (j : σ →₀ ℕ) :
    height (hasseDeriv j P) ≤ 2 ^ (∑ h, r h) * height P := by
  classical
  rw [height_le_iff]
  intro k
  rw [coeff_hasseDeriv, nsmul_eq_mul, Int.natAbs_mul, Int.natAbs_natCast]
  by_cases h0 : P.coeff (k + j) = 0
  · rw [h0]
    simp
  refine Nat.mul_le_mul ?_ (natAbs_coeff_le_height _ _)
  rw [Finsupp.prod_fintype _ _ (by simp), ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod fun h _ ↦ ?_
  have h1 := monomial_le_degreeOf h (mem_support_iff.mpr h0)
  simp only [Finsupp.add_apply] at h1
  calc (k h + j h).choose (j h) ≤ 2 ^ (k h + j h) := Nat.choose_le_two_pow _ _
    _ ≤ 2 ^ r h := Nat.pow_le_pow_right (by norm_num) (h1.trans (hP h))


/-! ### Generalized Wronskians -/

/-- Removing a linear dependence from a decomposition `P = ∑ f(φ_i) g(ψ_i)` ([schmidt1980],
Chapter V, p. 143). -/
lemma exists_shorter_decomposition {A M₁ M₂ : Type*} [CommRing A] [Algebra ℚ A]
    [AddCommGroup M₁] [Module ℚ M₁] [AddCommGroup M₂] [Module ℚ M₂] (f : M₁ →ₗ[ℚ] A)
    (g : M₂ →ₗ[ℚ] A) {n : ℕ} (φ : Fin (n + 1) → M₁) (ψ : Fin (n + 1) → M₂) (c : Fin (n + 1) → ℚ)
    (hc : ∑ i, c i • φ i = 0) (j : Fin (n + 1)) (hj : c j ≠ 0) :
    ∑ i, f (φ i) * g (ψ i) =
      ∑ i : Fin n, f (φ (j.succAbove i)) *
        g (ψ (j.succAbove i) - (c (j.succAbove i) / c j) • ψ j) := by
  have h1 : ∑ i : Fin n, c (j.succAbove i) • φ (j.succAbove i) = -(c j • φ j) := by
    have := hc
    rw [Fin.sum_univ_succAbove _ j] at this
    exact eq_neg_of_add_eq_zero_right this
  simp only [map_sub, map_smul, mul_sub, Finset.sum_sub_distrib]
  have h2 : ∑ i : Fin n, f (φ (j.succAbove i)) * ((c (j.succAbove i) / c j) • g (ψ j)) =
      -(f (φ j) * g (ψ j)) := by
    have : ∑ i : Fin n, f (φ (j.succAbove i)) * ((c (j.succAbove i) / c j) • g (ψ j)) =
        f ((c j)⁻¹ • ∑ i : Fin n, c (j.succAbove i) • φ (j.succAbove i)) * g (ψ j) := by
      rw [map_smul, map_sum, Finset.smul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul, smul_smul, smul_mul_assoc, mul_smul_comm, div_eq_inv_mul]
    rw [this, h1, smul_neg, smul_smul, inv_mul_cancel₀ hj, one_smul, map_neg, neg_mul]
  rw [h2, sub_neg_eq_add, Fin.sum_univ_succAbove _ j, add_comm]

/-- [schmidt1980], Chapter V, (10.8): a polynomial `P(X₁, …, Xₘ) ≠ 0` of degree at most `r` in
`Xₘ` can be written as `∑_{j < k} φ_j(X₁, …, X_{m-1}) ψ_j(Xₘ)` with `1 ≤ k ≤ r + 1`, where the
`φ_j` are linearly independent and the `ψ_j` are linearly independent (take `k` minimal). -/
theorem exists_tensor_decomposition (m : ℕ) (P : MvPolynomial (Fin (m + 1)) ℚ) (hP : P ≠ 0)
    (r : ℕ) (hr : P.degreeOf (Fin.last m) ≤ r) :
    ∃ (k : ℕ) (φ : Fin k → MvPolynomial (Fin m) ℚ) (ψ : Fin k → MvPolynomial (Fin 1) ℚ),
      0 < k ∧ k ≤ r + 1 ∧ LinearIndependent ℚ φ ∧ LinearIndependent ℚ ψ ∧
      P = ∑ i, rename Fin.castSucc (φ i) * rename (fun _ ↦ Fin.last m) (ψ i) := by
  classical
  set L : Fin 1 → Fin (m + 1) := fun _ ↦ Fin.last m with hL
  let Dec : ℕ → Prop := fun k ↦ ∃ (φ : Fin k → MvPolynomial (Fin m) ℚ)
    (ψ : Fin k → MvPolynomial (Fin 1) ℚ), P = ∑ i, rename Fin.castSucc (φ i) * rename L (ψ i)
  -- a decomposition with `k = r + 1`
  have hex : Dec (r + 1) := by
    set e := (renameEquiv ℚ (finRotate (m + 1))).trans (finSuccEquiv ℚ m) with he
    have hrot : ∀ i : Fin m, finRotate (m + 1) (Fin.castSucc i) = Fin.succ i := fun i ↦
      Fin.ext (by rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)]; simp)
    have he1 : ∀ φ : MvPolynomial (Fin m) ℚ, e (rename Fin.castSucc φ) = Polynomial.C φ := by
      intro φ
      induction φ using MvPolynomial.induction_on with
      | C a =>
        rw [rename_C]
        exact e.commutes a
      | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
      | mul_X p i hp =>
        rw [map_mul, map_mul, hp, rename_X, map_mul]
        congr 1
        simp only [he, AlgEquiv.trans_apply, renameEquiv_apply, rename_X, hrot,
          finSuccEquiv_X_succ]
    have he2 : e (X (Fin.last m)) = Polynomial.X := by
      simp only [he, AlgEquiv.trans_apply, renameEquiv_apply, rename_X, finRotate_last,
        finSuccEquiv_X_zero]
    have hdeg : (e P).natDegree < r + 1 := by
      simp only [he, AlgEquiv.trans_apply, renameEquiv_apply]
      rw [natDegree_finSuccEquiv, ← finRotate_last,
        degreeOf_rename_of_injective (finRotate (m + 1)).injective]
      omega
    refine ⟨fun t ↦ (e P).coeff t, fun t ↦ X 0 ^ (t : ℕ), ?_⟩
    apply e.injective
    conv_lhs => rw [Polynomial.as_sum_range' _ _ hdeg]
    rw [map_sum, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    have he2' : e (X (L 0)) = Polynomial.X := he2
    rw [map_mul, he1, map_pow, rename_X, map_pow, he2', Polynomial.C_mul_X_pow_eq_monomial]
  -- a decomposition with `k` minimal
  have hD : ∃ k, Dec k := ⟨r + 1, hex⟩
  have hle : Nat.find hD ≤ r + 1 := Nat.find_min' hD hex
  have hmin : ∀ k < Nat.find hD, ¬ Dec k := fun k hk ↦ Nat.find_min hD hk
  obtain ⟨φ, ψ, hdec⟩ := Nat.find_spec hD
  generalize Nat.find hD = k₀ at hle hmin φ ψ hdec
  cases k₀ with
  | zero =>
    exact absurd (by simpa using hdec) hP
  | succ n =>
    refine ⟨n + 1, φ, ψ, Nat.succ_pos n, hle, ?_, ?_, hdec⟩
    · by_contra h
      rw [Fintype.not_linearIndependent_iff] at h
      obtain ⟨c, hc, j, hj⟩ := h
      apply hmin n (Nat.lt_succ_self n)
      refine ⟨fun i ↦ φ (j.succAbove i),
        fun i ↦ ψ (j.succAbove i) - (c (j.succAbove i) / c j) • ψ j, ?_⟩
      rw [hdec]
      exact exists_shorter_decomposition (rename Fin.castSucc).toLinearMap
        (rename L).toLinearMap φ ψ c hc j hj
    · by_contra h
      rw [Fintype.not_linearIndependent_iff] at h
      obtain ⟨c, hc, j, hj⟩ := h
      apply hmin n (Nat.lt_succ_self n)
      refine ⟨fun i ↦ φ (j.succAbove i) - (c (j.succAbove i) / c j) • φ j,
        fun i ↦ ψ (j.succAbove i), ?_⟩
      have := exists_shorter_decomposition (rename L).toLinearMap
        (rename Fin.castSucc).toLinearMap ψ φ c hc j hj
      rw [hdec]
      simp only [AlgHom.toLinearMap_apply] at this
      simp_rw [mul_comm (rename Fin.castSucc _)]
      exact this

/-- The divided derivative of a product by a polynomial not involving the variables of the
derivative. -/
lemma hasseDeriv_mul_of_disjoint {σ R : Type*} [CommRing R] (A : σ →₀ ℕ)
    (F G : MvPolynomial σ R) (hG : ∀ g ∈ G.support, ∀ v ∈ A.support, g v = 0) :
    hasseDeriv A (F * G) = hasseDeriv A F * G := by
  classical
  rw [F.as_sum, G.as_sum]
  simp only [← hasseDerivₗ_apply, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun f _ ↦ Finset.sum_congr rfl fun g hg ↦ ?_
  rw [hasseDerivₗ_apply, hasseDerivₗ_apply, monomial_mul_monomial, hasseDeriv_monomial,
    hasseDeriv_monomial, monomial_mul_monomial]
  have hgA : ∀ v ∈ A.support, g v = 0 := hG g hg
  have he : f + g - A = f - A + g := by
    refine Finsupp.ext fun v ↦ ?_
    rw [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.add_apply, Finsupp.tsub_apply]
    by_cases hv : v ∈ A.support
    · rw [hgA v hv]; simp
    · rw [Finsupp.notMem_support_iff.mp hv]; simp
  rw [he]
  congr 1
  rw [smul_mul_assoc]
  congr 1
  refine Finset.prod_congr rfl fun v hv ↦ ?_
  simp only [Finsupp.add_apply, hgA v hv, add_zero]

/-- The product rule for divided derivatives of a product `φ(X₁, …, X_{m-1}) ψ(Xₘ)` of
polynomials in disjoint sets of variables. -/
theorem hasseDeriv_rename_mul_rename {R : Type*} [CommRing R] (m : ℕ) (a : Fin m →₀ ℕ)
    (b : Fin 1 →₀ ℕ) (φ : MvPolynomial (Fin m) R) (ψ : MvPolynomial (Fin 1) R) :
    hasseDeriv (a.mapDomain Fin.castSucc + b.mapDomain fun _ ↦ Fin.last m)
        (rename Fin.castSucc φ * rename (fun _ ↦ Fin.last m) ψ) =
      rename Fin.castSucc (hasseDeriv a φ) * rename (fun _ ↦ Fin.last m) (hasseDeriv b ψ) := by
  classical
  have hinj1 : Function.Injective (fun _ : Fin 1 ↦ Fin.last m) := fun x y _ ↦
    Subsingleton.elim x y
  set A := a.mapDomain Fin.castSucc with hAdef
  set B := b.mapDomain fun _ : Fin 1 ↦ Fin.last m with hBdef
  have hA : ∀ v ∈ A.support, v ≠ Fin.last m := fun v hv h ↦ by
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hv)
    exact Fin.castSucc_ne_last u h
  have hB : ∀ v ∈ B.support, v = Fin.last m := fun v hv ↦ by
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hv)
    rfl
  have hsuppψ : ∀ g ∈ (rename (fun _ : Fin 1 ↦ Fin.last m) ψ).support, ∀ v ∈ A.support,
      g v = 0 := by
    intro g hg v hv
    rw [support_rename_of_injective hinj1] at hg
    obtain ⟨g', -, rfl⟩ := Finset.mem_image.mp hg
    exact Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨u, rfl⟩; exact hA _ hv rfl)
  have hsuppφ : ∀ g ∈ (rename Fin.castSucc (hasseDeriv a φ)).support, ∀ v ∈ B.support,
      g v = 0 := by
    intro g hg v hv
    rw [support_rename_of_injective (Fin.castSucc_injective m)] at hg
    obtain ⟨g', -, rfl⟩ := Finset.mem_image.mp hg
    rw [hB v hv]
    exact Finsupp.mapDomain_of_notMem_range _ _ (by
      rintro ⟨u, hu⟩
      exact Fin.castSucc_ne_last u hu)
  have hdisj : ∀ v, A v = 0 ∨ B v = 0 := fun v ↦ by
    by_cases hv : v = Fin.last m
    · left
      by_contra h
      exact hA v (Finsupp.mem_support_iff.mpr h) hv
    · right
      by_contra h
      exact hv (hB v (Finsupp.mem_support_iff.mpr h))
  rw [← hasseDeriv_hasseDeriv_of_disjoint hdisj, hasseDeriv_mul_of_disjoint A _ _ hsuppψ,
    hAdef, hasseDeriv_rename (Fin.castSucc_injective m), mul_comm,
    hasseDeriv_mul_of_disjoint B _ _ hsuppφ, hBdef, hasseDeriv_rename hinj1, mul_comm]

/-- The generalized Wronskian of [schmidt1980], Chapter V, pp. 142–144. Write
`P = ∑_{j ≤ k} φ_j(X₁, …, X_{m-1}) ψ_j(Xₘ)` with `k` minimal (so that `k ≤ rₘ + 1` and the `φ_j`,
resp. the `ψ_j`, are linearly independent, (10.8)), and choose by Lemma 9A operators `Δ'_i` of
order at most `i - 1` in `X₁, …, X_{m-1}` and orders `e_j ≤ j - 1` in `Xₘ` with non-vanishing
generalized Wronskians `V = det(Δ'_i φ_j)`, `U = det(∂^{e_j} ψ_i)`. Then
`W = det(P_{Δ'_i, e_j}) = V(X₁, …, X_{m-1}) U(Xₘ) ≠ 0`. -/
theorem exists_wronskian (m : ℕ) (P : MvPolynomial (Fin (m + 1)) ℤ) (hP : P ≠ 0) (r : ℕ)
    (hr : P.degreeOf (Fin.last m) ≤ r) :
    ∃ (k : ℕ) (D : Fin k → Fin (m + 1) →₀ ℕ) (E : Fin k → ℕ), 0 < k ∧ k ≤ r + 1 ∧
      (∀ i, D i (Fin.last m) = 0) ∧ (∀ i, (D i).degree ≤ i) ∧ (∀ j, E j ≤ j) ∧
      ∃ (V : MvPolynomial (Fin m) ℚ) (U : MvPolynomial (Fin 1) ℚ), V ≠ 0 ∧ U ≠ 0 ∧
        map (Int.castRingHom ℚ)
          (Matrix.of fun i j ↦ hasseDeriv (D i + Finsupp.single (Fin.last m) (E j)) P).det =
          rename Fin.castSucc V * rename (fun _ ↦ Fin.last m) U := by
  classical
  set F := map (Int.castRingHom ℚ) P with hF
  have hF0 : F ≠ 0 := fun h0 ↦ hP (map_injective _ Int.cast_injective (by rw [← hF, h0, map_zero]))
  have hFr : F.degreeOf (Fin.last m) ≤ r := by
    rw [degreeOf_le_iff]
    intro j hj
    exact (degreeOf_le_iff.mp hr) j (support_map_subset _ _ hj)
  obtain ⟨k, φ, ψ, hk0, hkr, hφ, hψ, hdec⟩ := exists_tensor_decomposition m F hF0 r hFr
  obtain ⟨D, hD, hV⟩ := exists_wronskian_ne_zero φ hφ
  obtain ⟨E, hE, hU⟩ := exists_wronskian_ne_zero ψ hψ
  have hE1 : ∀ j, E j = Finsupp.single 0 (E j 0) := fun j ↦ by
    refine Finsupp.ext fun i ↦ ?_
    rw [Subsingleton.elim i 0, Finsupp.single_eq_same]
  refine ⟨k, fun i ↦ (D i).mapDomain Fin.castSucc, fun j ↦ E j 0, hk0, hkr, fun i ↦ ?_,
    fun i ↦ ?_, fun j ↦ ?_, (Matrix.of fun i l ↦ hasseDeriv (D i) (φ l)).det,
    (Matrix.of fun j l ↦ hasseDeriv (E j) (ψ l)).det, hV, hU, ?_⟩
  · exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)
  · rw [Finsupp.degree_mapDomain]
    exact hD i
  · have := hE j
    rwa [Finsupp.degree_eq_sum, Fin.sum_univ_one] at this
  · rw [RingHom.map_det]
    have hM : (map (Int.castRingHom ℚ)).mapMatrix (Matrix.of fun i j ↦
        hasseDeriv ((D i).mapDomain Fin.castSucc + Finsupp.single (Fin.last m) (E j 0)) P) =
        (Matrix.of fun i l ↦ rename Fin.castSucc (hasseDeriv (D i) (φ l))) *
        (Matrix.of fun j l ↦
          rename (fun _ : Fin 1 ↦ Fin.last m) (hasseDeriv (E j) (ψ l))).transpose := by
      refine Matrix.ext fun i j ↦ ?_
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_hasseDeriv, ← hF, hdec,
        Matrix.mul_apply]
      rw [← hasseDerivₗ_apply, map_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      simp only [Matrix.of_apply, Matrix.transpose_apply, hasseDerivₗ_apply]
      rw [← hasseDeriv_rename_mul_rename, hE1 j, Finsupp.mapDomain_single, ← hE1 j]
    rw [hM, Matrix.det_mul, Matrix.det_transpose]
    have h1 : (Matrix.of fun i l ↦ rename Fin.castSucc (hasseDeriv (D i) (φ l))).det =
        rename Fin.castSucc (Matrix.of fun i l ↦ hasseDeriv (D i) (φ l)).det := by
      rw [AlgHom.map_det]
      rfl
    have h2 : (Matrix.of fun j l ↦
        rename (fun _ : Fin 1 ↦ Fin.last m) (hasseDeriv (E j) (ψ l))).det =
        rename (fun _ : Fin 1 ↦ Fin.last m) (Matrix.of fun j l ↦ hasseDeriv (E j) (ψ l)).det := by
      rw [AlgHom.map_det]
      rfl
    rw [h1, h2]

/-- The coefficients of a product `V(X₁, …, X_{m-1}) U(Xₘ)`. -/
lemma coeff_rename_mul_rename {R : Type*} [CommRing R] (m : ℕ) (V : MvPolynomial (Fin m) R)
    (U : MvPolynomial (Fin 1) R) (a : Fin m →₀ ℕ) (b : Fin 1 →₀ ℕ) :
    (rename Fin.castSucc V * rename (fun _ ↦ Fin.last m) U).coeff
      (a.mapDomain Fin.castSucc + b.mapDomain fun _ ↦ Fin.last m) = V.coeff a * U.coeff b := by
  classical
  have hinj1 : Function.Injective (fun _ : Fin 1 ↦ Fin.last m) := fun x y _ ↦
    Subsingleton.elim x y
  conv_lhs => rw [U.as_sum, map_sum, Finset.mul_sum, coeff_sum]
  simp only [rename_monomial, coeff_mul_monomial']
  rw [Finset.sum_eq_single b]
  · rw [ite_eq_left (le_add_self), add_tsub_cancel_right,
      coeff_rename_mapDomain _ (Fin.castSucc_injective m)]
  · intro b' _ hb'
    split_ifs with hle
    · rw [coeff_rename_eq_zero _ _ _ fun u hu ↦ ?_, zero_mul]
      exfalso
      apply hb'
      have hlast : ∀ c : Fin 1 →₀ ℕ, (c.mapDomain fun _ ↦ Fin.last m) (Fin.last m) = c 0 :=
        fun c ↦ Finsupp.mapDomain_apply_of_injective hinj1 c 0
      have hA : (a.mapDomain Fin.castSucc) (Fin.last m) = 0 :=
        Finsupp.mapDomain_of_notMem_range _ _ (by simp)
      have hU : (u.mapDomain Fin.castSucc) (Fin.last m) = 0 :=
        Finsupp.mapDomain_of_notMem_range _ _ (by simp)
      have h1 := congrArg (fun f ↦ f (Fin.last m)) hu
      have h2 := hle (Fin.last m)
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, hA, hU, hlast, zero_add] at h1 h2
      refine Finsupp.ext fun i ↦ ?_
      rw [Subsingleton.elim i 0]
      omega
    · rfl
  · intro hb
    rw [notMem_support_iff.mp hb]
    simp

/-- A rational number `x` such that `x u_b` is an integer for integers `u_b` with
`gcd(u_b) = 1` is an integer. -/
lemma exists_int_of_mul_int {ι : Type*} (s : Finset ι) (u : ι → ℤ) (hu : s.gcd u = 1) (x : ℚ)
    (hx : ∀ b ∈ s, ∃ n : ℤ, x * u b = n) : ∃ n : ℤ, x = n := by
  refine ⟨x.num, ?_⟩
  have hd : ∀ b ∈ s, (x.den : ℤ) ∣ u b := by
    intro b hb
    obtain ⟨n, hn⟩ := hx b hb
    have h1 : (x.num : ℚ) * u b = n * x.den := by
      rw [← Rat.mul_den_eq_num, mul_right_comm, hn]
    have h2 : x.num * u b = n * x.den := by exact_mod_cast h1
    have h3 : (x.den : ℤ) ∣ x.num * u b := ⟨n, by rw [h2, mul_comm]⟩
    exact (Int.isCoprime_iff_gcd_eq_one.mpr (by
      rw [Int.gcd_comm]
      exact x.reduced)).dvd_of_dvd_mul_left h3
  have h4 : (x.den : ℤ) ∣ s.gcd u := Finset.dvd_gcd hd
  rw [hu] at h4
  have h5 : x.den = 1 := by
    have := Int.eq_one_of_dvd_one (by positivity) h4
    exact_mod_cast this
  rw [← Rat.num_div_den x, h5]
  simp

/-- [schmidt1980], Chapter V, p. 145: a factorization `W = V(X₁, …, X_{m-1}) U(Xₘ)` over `ℚ`
of a polynomial `W` with integer coefficients can be chosen with integer factors (Gauss's lemma);
their heights are then at most `|W|`, and their degrees at most those of `W`. -/
theorem exists_int_factorization (m : ℕ) (W : MvPolynomial (Fin (m + 1)) ℤ)
    (V : MvPolynomial (Fin m) ℚ) (U : MvPolynomial (Fin 1) ℚ) (hV : V ≠ 0) (hU : U ≠ 0)
    (hW : map (Int.castRingHom ℚ) W = rename Fin.castSucc V * rename (fun _ ↦ Fin.last m) U) :
    ∃ (V' : MvPolynomial (Fin m) ℤ) (U' : MvPolynomial (Fin 1) ℤ), V' ≠ 0 ∧ U' ≠ 0 ∧
      W = rename Fin.castSucc V' * rename (fun _ ↦ Fin.last m) U' ∧
      height V' ≤ height W ∧ height U' ≤ height W ∧
      (∀ h, V'.degreeOf h ≤ W.degreeOf (Fin.castSucc h)) ∧
      U'.degreeOf 0 ≤ W.degreeOf (Fin.last m) := by
  classical
  set L : Fin 1 → Fin (m + 1) := fun _ ↦ Fin.last m with hL
  have hinj1 : Function.Injective L := fun x y _ ↦ Subsingleton.elim x y
  set E : (Fin m →₀ ℕ) → (Fin 1 →₀ ℕ) → (Fin (m + 1) →₀ ℕ) :=
    fun a b ↦ a.mapDomain Fin.castSucc + b.mapDomain L with hE
  have hcoef : ∀ a b, ((W.coeff (E a b) : ℤ) : ℚ) = V.coeff a * U.coeff b := by
    intro a b
    have := congrArg (fun F ↦ F.coeff (E a b)) hW
    simp only [coeff_map, eq_intCast] at this
    rw [this, hE, coeff_rename_mul_rename]
  have hEc : ∀ a b (h : Fin m), E a b (Fin.castSucc h) = a h := fun a b h ↦ by
    simp only [hE, Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective
      (Fin.castSucc_injective m)]
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by
      rintro ⟨u, hu⟩
      exact Fin.castSucc_ne_last h hu.symm), add_zero]
  have hEl : ∀ a b, E a b (Fin.last m) = b 0 := fun a b ↦ by
    simp only [hE, Finsupp.add_apply]
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp), zero_add]
    exact Finsupp.mapDomain_apply_of_injective hinj1 b 0
  obtain ⟨a₀, ha₀⟩ := ne_zero_iff.mp hV
  obtain ⟨b₀, hb₀⟩ := ne_zero_iff.mp hU
  set w : (Fin 1 →₀ ℕ) → ℤ := fun b ↦ W.coeff (E a₀ b) with hw
  obtain ⟨u', hu', hgcd⟩ := Finset.extract_gcd w (s := U.support) ⟨b₀, mem_support_iff.mpr hb₀⟩
  set g := U.support.gcd w with hg
  have hwb₀ : w b₀ ≠ 0 := by
    intro h0
    have := hcoef a₀ b₀
    rw [show W.coeff (E a₀ b₀) = w b₀ from rfl, h0, Int.cast_zero] at this
    exact mul_ne_zero ha₀ hb₀ this.symm
  have hg0 : g ≠ 0 := by
    intro h0
    apply hwb₀
    rw [hu' b₀ (mem_support_iff.mpr hb₀), h0, zero_mul]
  have hu'b₀ : u' b₀ ≠ 0 := by
    intro h0
    apply hwb₀
    rw [hu' b₀ (mem_support_iff.mpr hb₀), h0, mul_zero]
  set c : ℚ := (g : ℚ) / V.coeff a₀ with hc
  have hc0 : c ≠ 0 := div_ne_zero (by exact_mod_cast hg0) ha₀
  -- the coefficients of `U` are `u'_b / c`
  have hUb : ∀ b ∈ U.support, U.coeff b = c * u' b := by
    intro b hb
    have h1 := hcoef a₀ b
    rw [show W.coeff (E a₀ b) = w b from rfl, hu' b hb] at h1
    rw [hc]
    push_cast at h1
    field_simp
    linear_combination -h1
  -- the coefficients of `c V` are integers
  have hint : ∀ a, ∃ n : ℤ, c * V.coeff a = n := fun a ↦
    exists_int_of_mul_int U.support u' hgcd (c * V.coeff a) fun b hb ↦
      ⟨W.coeff (E a b), by rw [hcoef, hUb b hb]; ring⟩
  choose nV hnV using hint
  have hWnV : ∀ a, ∀ b ∈ U.support, nV a * u' b = W.coeff (E a b) := fun a b hb ↦ by
    have : ((nV a * u' b : ℤ) : ℚ) = W.coeff (E a b) := by
      rw [hcoef, hUb b hb]
      push_cast
      rw [← hnV a]
      ring
    exact_mod_cast this
  set U' : MvPolynomial (Fin 1) ℤ := ∑ b ∈ U.support, monomial b (u' b) with hU'
  set V' : MvPolynomial (Fin m) ℤ := ∑ a ∈ V.support, monomial a (nV a) with hV'
  have hU'c : ∀ b, U'.coeff b = if b ∈ U.support then u' b else 0 := fun b ↦ by
    simp only [hU', coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
  have hV'c : ∀ a, V'.coeff a = if a ∈ V.support then nV a else 0 := fun a ↦ by
    simp only [hV', coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
  have hmapU : map (Int.castRingHom ℚ) U' = c⁻¹ • U := by
    ext b
    rw [coeff_map, hU'c, coeff_smul, smul_eq_mul]
    split_ifs with hb
    · rw [hUb b hb, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
      simp
    · rw [notMem_support_iff.mp hb]
      simp
  have hmapV : map (Int.castRingHom ℚ) V' = c • V := by
    ext a
    rw [coeff_map, hV'c, coeff_smul, smul_eq_mul]
    split_ifs with ha
    · rw [hnV a]
      simp
    · rw [notMem_support_iff.mp ha]
      simp
  refine ⟨V', U', fun h0 ↦ ?_, fun h0 ↦ ?_, ?_, ?_, ?_, fun h ↦ ?_, ?_⟩
  · have := hV'c a₀
    rw [h0, ite_eq_left (mem_support_iff.mpr ha₀)] at this
    replace this : nV a₀ = 0 := by simpa using this.symm
    have h1 := hnV a₀
    rw [this, Int.cast_zero] at h1
    exact mul_ne_zero hc0 ha₀ h1
  · have := hU'c b₀
    rw [h0, ite_eq_left (mem_support_iff.mpr hb₀)] at this
    exact hu'b₀ (by simpa using this.symm)
  · apply map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [hW, map_mul, map_rename, map_rename, hmapV, hmapU, map_smul, map_smul,
      smul_mul_smul_comm, mul_inv_cancel₀ hc0, one_smul]
  · rw [height_le_iff]
    intro a
    rw [hV'c]
    split_ifs with ha
    · calc (nV a).natAbs ≤ (nV a).natAbs * (u' b₀).natAbs :=
            Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hu'b₀)
        _ = (W.coeff (E a b₀)).natAbs := by
            rw [← Int.natAbs_mul, hWnV a b₀ (mem_support_iff.mpr hb₀)]
        _ ≤ height W := natAbs_coeff_le_height _ _
    · simp
  · rw [height_le_iff]
    intro b
    rw [hU'c]
    split_ifs with hb
    · calc (u' b).natAbs ≤ g.natAbs * (u' b).natAbs :=
            Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr hg0)
        _ = (W.coeff (E a₀ b)).natAbs := by
            rw [← Int.natAbs_mul, ← hu' b hb]
        _ ≤ height W := natAbs_coeff_le_height _ _
    · simp
  · rw [degreeOf_le_iff]
    intro a ha
    have ha' : a ∈ V.support := by
      by_contra h
      rw [mem_support_iff, hV'c, ite_eq_right h] at ha
      exact ha rfl
    have hne : W.coeff (E a b₀) ≠ 0 := by
      rw [← hWnV a b₀ (mem_support_iff.mpr hb₀)]
      refine mul_ne_zero (fun h0 ↦ ?_) hu'b₀
      have := hnV a
      rw [h0, Int.cast_zero] at this
      exact mul_ne_zero hc0 (mem_support_iff.mp ha') this
    have := monomial_le_degreeOf (Fin.castSucc h) (mem_support_iff.mpr hne)
    rwa [hEc] at this
  · rw [degreeOf_le_iff]
    intro b hb
    have hb' : b ∈ U.support := by
      by_contra h
      rw [mem_support_iff, hU'c, ite_eq_right h] at hb
      exact hb rfl
    have hne : W.coeff (E a₀ b) ≠ 0 := by
      rw [show W.coeff (E a₀ b) = w b from rfl, hu' b hb']
      exact mul_ne_zero hg0 (fun h0 ↦ by
        rw [mem_support_iff, hU'c, ite_eq_left hb', h0] at hb
        exact hb rfl)
    have := monomial_le_degreeOf (Fin.last m) (mem_support_iff.mpr hne)
    rwa [hEl] at this

/-- The height and the degrees of a determinant of divided derivatives of `P`
([schmidt1980], Chapter V, p. 145, using Lemma 5A): if `P` has degree at most `r_h ≤ r₁` in `X_h`
and `k ≤ rₘ + 1`, then `|det(P_{D i j})| ≤ (2 ^ (3 m r₁) |P|) ^ k`, and the determinant has degree
at most `k r_h` in `X_h`. -/
theorem height_det_hasseDeriv_le (m : ℕ) (P : MvPolynomial (Fin (m + 1)) ℤ)
    (r : Fin (m + 1) → ℕ) (hdeg : ∀ h, P.degreeOf h ≤ r h) (hr0 : ∀ h, r h ≤ r 0) (k : ℕ)
    (hk : k ≤ r (Fin.last m) + 1) (D : Fin k → Fin k → Fin (m + 1) →₀ ℕ) :
    height (Matrix.of fun i j ↦ hasseDeriv (D i j) P).det ≤
        (2 ^ (3 * (m + 1) * r 0) * height P) ^ k ∧
      ∀ h, (Matrix.of fun i j ↦ hasseDeriv (D i j) P).det.degreeOf h ≤ k * r h := by
  classical
  set M := Matrix.of fun i j ↦ hasseDeriv (D i j) P with hM
  set S := ∑ h, r h with hS
  have hdeg' : ∀ i j h, (M i j).degreeOf h ≤ r h := fun i j h ↦
    (degreeOf_hasseDeriv_le P (D i j) h).trans (hdeg h)
  have hentry : ∀ i j, (M i j).support.card * height (M i j) ≤ 2 ^ S * (2 ^ S * height P) :=
    fun i j ↦ Nat.mul_le_mul (card_support_le _ r (hdeg' i j)) (height_hasseDeriv_le P r hdeg _)
  have hSle : S ≤ (m + 1) * r 0 := by
    have := Finset.sum_le_card_nsmul Finset.univ r (r 0) (fun h _ ↦ hr0 h)
    simpa using this
  have hkfac : k.factorial ≤ (2 ^ r (Fin.last m)) ^ k := by
    refine (Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left ?_ k)
    exact hk.trans (Nat.lt_two_pow_self)
  refine ⟨?_, fun h ↦ ?_⟩
  · rw [Matrix.det_apply]
    calc height (∑ τ : Equiv.Perm (Fin k), Equiv.Perm.sign τ • ∏ i, M (τ i) i)
        ≤ ∑ τ : Equiv.Perm (Fin k), height (Equiv.Perm.sign τ • ∏ i, M (τ i) i) :=
          height_sum_le _ _
      _ = ∑ τ : Equiv.Perm (Fin k), height (∏ i, M (τ i) i) :=
          Finset.sum_congr rfl fun τ _ ↦ height_units_smul _ _
      _ ≤ ∑ τ : Equiv.Perm (Fin k), ∏ i, ((M (τ i) i).support.card * height (M (τ i) i)) :=
          Finset.sum_le_sum fun τ _ ↦ height_prod_le _ _
      _ ≤ ∑ _τ : Equiv.Perm (Fin k), ∏ _i : Fin k, 2 ^ S * (2 ^ S * height P) :=
          Finset.sum_le_sum fun τ _ ↦ Finset.prod_le_prod fun i _ ↦ hentry _ _
      _ = k.factorial * (2 ^ S * (2 ^ S * height P)) ^ k := by
          rw [Finset.sum_const, Finset.prod_const, Finset.card_univ, Finset.card_univ,
            Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
      _ ≤ (2 ^ r (Fin.last m)) ^ k * (2 ^ S * (2 ^ S * height P)) ^ k :=
          Nat.mul_le_mul_right _ hkfac
      _ = (2 ^ (r (Fin.last m) + 2 * S) * height P) ^ k := by
          rw [← mul_pow]
          congr 1
          rw [pow_add, two_mul, pow_add]
          ring
      _ ≤ (2 ^ (3 * (m + 1) * r 0) * height P) ^ k := by
          refine Nat.pow_le_pow_left (Nat.mul_le_mul_right _
            (Nat.pow_le_pow_right (by norm_num) ?_)) k
          have := hr0 (Fin.last m)
          nlinarith
  · rw [Matrix.det_apply]
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun τ _ ↦ ?_)
    rw [Units.smul_def, smul_eq_C_mul]
    refine (degreeOf_C_mul_le _ _ _).trans ((degreeOf_prod_le _ _ _).trans ?_)
    calc ∑ i, (M (τ i) i).degreeOf h ≤ ∑ _i : Fin k, r h :=
          Finset.sum_le_sum fun i _ ↦ hdeg' _ _ _
      _ = k * r h := by simp


end Schmidt
