module

public import Heights.SubspaceTheorem.HasseTaylor

/-!
# Generalized Wronskians

We prove [schmidt1980], Chapter V, Lemma 9A (`Schmidt.exists_wronskian_ne_zero`): if the
polynomials `φ₁, …, φ_k ∈ ℚ[X_t : t ∈ τ]` are linearly independent over `ℚ`, there are divided
derivatives `Δ_i` of order at most `i - 1` such that `det(Δ_i φ_j) ≠ 0`.

The proof avoids fraction fields. Choose Kronecker weights `w : τ → ℕ` such that
`α ↦ λ_α = ∑_t w_t α_t` is injective on the exponents occurring in the `φ_j`, and consider the
Euler operator `E = ∑_t w_t X_t ∂/∂X_t`, which multiplies `X ^ α` by `λ_α`.

* The specialization `X_t ↦ s ^ w_t` turns `E` into `s d/ds` and is injective on the span of the
  `φ_j`; a Vandermonde argument then shows that `det(E^i φ_j) ≠ 0`.
* The row `(E^i φ_j)_j` lies in the span (over the polynomial ring) of the rows
  `(Δ_β φ_j)_j` with `|β| ≤ i`; expanding the determinant multilinearly in its rows, one of the
  determinants `det(Δ_{β_i} φ_j)` with `|β_i| ≤ i` does not vanish.
-/

@[expose] public section

namespace Schmidt

open MvPolynomial

section GeneralizedWronskian

variable {τ : Type*}

/-! ### Kronecker weights -/

/-- Kronecker weights: there is `w : τ → ℕ` such that `α ↦ ∑_t w_t α_t` is injective on the
exponents `α` with `α_t < N` for every `t`. -/
lemma exists_kronecker_weights [Fintype τ] (N : ℕ) :
    ∃ w : τ → ℕ, ∀ α β : τ →₀ ℕ, (∀ t, α t < N) → (∀ t, β t < N) →
      ∑ t, w t * α t = ∑ t, w t * β t → α = β := by
  classical
  let e := Fintype.equivFin τ
  refine ⟨fun t ↦ N ^ (e t : ℕ), fun α β hα hβ h ↦ ?_⟩
  have key : ∀ (γ : τ →₀ ℕ) (hγ : ∀ t, γ t < N), ∑ t, N ^ (e t : ℕ) * γ t =
      (finFunctionFinEquiv (fun m ↦ (⟨γ (e.symm m), hγ _⟩ : Fin N)) : ℕ) := by
    intro γ hγ
    rw [finFunctionFinEquiv_apply]
    exact Fintype.sum_equiv e _ _ fun t ↦ by simp [mul_comm]
  have h1 := finFunctionFinEquiv.injective (Fin.ext ((key α hα).symm.trans (h.trans (key β hβ))))
  ext t
  have h2 := congrArg Fin.val (congrFun h1 (e t))
  simpa using h2

/-! ### The Euler operator and the Kronecker specialization -/

/-- The weighted Euler operator `∑_t w_t X_t ∂/∂X_t`. -/
noncomputable def eulerOp [Fintype τ] (w : τ → ℕ) :
    Derivation ℚ (MvPolynomial τ ℚ) (MvPolynomial τ ℚ) :=
  ∑ t, (C (w t : ℚ) * X t) • pderiv t

lemma eulerOp_apply [Fintype τ] (w : τ → ℕ) (p : MvPolynomial τ ℚ) :
    eulerOp w p = ∑ t, C (w t : ℚ) * X t * pderiv t p := by
  rw [eulerOp, ← FunLike.coeAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

lemma eulerOp_monomial [Fintype τ] (w : τ → ℕ) (α : τ →₀ ℕ) (c : ℚ) :
    eulerOp w (monomial α c) = ((∑ t, w t * α t : ℕ) : ℚ) • monomial α c := by
  rw [eulerOp_apply, Nat.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [mul_assoc, X_mul_pderiv_monomial, smul_eq_C_mul, nsmul_eq_mul, ← C_eq_natCast,
    ← mul_assoc, ← C_mul, Nat.cast_mul]

/-- The Kronecker specialization `X_t ↦ s ^ w_t`. -/
noncomputable def kron (w : τ → ℕ) : MvPolynomial τ ℚ →ₐ[ℚ] Polynomial ℚ :=
  aeval fun t ↦ Polynomial.X ^ w t

/-- The operator `s d/ds` on `ℚ[s]`. -/
noncomputable def polyEuler : Polynomial ℚ →ₗ[ℚ] Polynomial ℚ :=
  (LinearMap.mulLeft ℚ Polynomial.X).comp Polynomial.derivative

lemma polyEuler_monomial (n : ℕ) (c : ℚ) :
    polyEuler (Polynomial.monomial n c) = (n : ℚ) • Polynomial.monomial n c := by
  rw [polyEuler, LinearMap.comp_apply, Polynomial.derivative_monomial, LinearMap.mulLeft_apply,
    Polynomial.X_mul_monomial, Polynomial.smul_monomial, smul_eq_mul, mul_comm]
  rcases n with _ | n
  · simp
  · rfl

lemma kron_monomial [Fintype τ] (w : τ → ℕ) (α : τ →₀ ℕ) (c : ℚ) :
    kron w (monomial α c) = Polynomial.monomial (∑ t, w t * α t) c := by
  rw [kron, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
  rfl

lemma kron_eulerOp [Fintype τ] (w : τ → ℕ) (p : MvPolynomial τ ℚ) :
    kron w (eulerOp w p) = polyEuler (kron w p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [eulerOp_monomial, map_smul, kron_monomial, polyEuler_monomial]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

lemma eq_zero_of_kron_eq_zero [Fintype τ] {w : τ → ℕ} {N : ℕ}
    (hw : ∀ α β : τ →₀ ℕ, (∀ t, α t < N) → (∀ t, β t < N) →
      ∑ t, w t * α t = ∑ t, w t * β t → α = β)
    (p : MvPolynomial τ ℚ) (hp : ∀ α ∈ p.support, ∀ t, α t < N) (h0 : kron w p = 0) :
    p = 0 := by
  classical
  by_contra hne
  obtain ⟨α₀, hα₀⟩ := ne_zero_iff.mp hne
  have hmem : α₀ ∈ p.support := mem_support_iff.mpr hα₀
  have := congrArg (fun q : Polynomial ℚ ↦ q.coeff (∑ t, w t * α₀ t)) h0
  simp only [Polynomial.coeff_zero] at this
  rw [p.as_sum, map_sum (kron w), Polynomial.finsetSum_coeff, Finset.sum_eq_single α₀] at this
  · rw [kron_monomial, Polynomial.coeff_monomial_same] at this
    exact hα₀ this
  · intro β hβ hne'
    rw [kron_monomial, Polynomial.coeff_monomial, Finsupp.single_eq_of_ne]
    refine fun heq ↦ hne' (hw β α₀ (hp β hβ) (hp α₀ hmem) ?_)
    exact heq.symm
  · intro h
    exact absurd hmem h

/-! ### The one-variable case -/

lemma coeff_polyEuler (q : Polynomial ℚ) (m : ℕ) : (polyEuler q).coeff m = m * q.coeff m := by
  rcases m with _ | m
  · simp [polyEuler]
  · rw [polyEuler, LinearMap.comp_apply, LinearMap.mulLeft_apply, Polynomial.coeff_X_mul,
      Polynomial.coeff_derivative]
    push_cast
    ring

lemma coeff_polyEuler_iterate (q : Polynomial ℚ) (i m : ℕ) :
    ((⇑polyEuler)^[i] q).coeff m = (m : ℚ) ^ i * q.coeff m := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', coeff_polyEuler, ih]
    ring

lemma natDegree_polyEuler_iterate_le (q : Polynomial ℚ) (i : ℕ) :
    ((⇑polyEuler)^[i] q).natDegree ≤ q.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_polyEuler_iterate, Polynomial.coeff_eq_zero_of_natDegree_lt hm, mul_zero]

lemma coeff_prod_of_natDegree_le' {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℚ) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (h a (Finset.mem_insert_self a s)),
      ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)]
    exact (Polynomial.natDegree_prod_le _ _).trans
      (Finset.sum_le_sum fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- `det((s d/ds)^i p_j) ≠ 0` if the `p_j` are non-zero of pairwise distinct degrees. -/
lemma det_polyEuler_ne_zero_of_injective {k : ℕ} (p : Fin k → Polynomial ℚ) (hp : ∀ j, p j ≠ 0)
    (hd : Function.Injective fun j ↦ (p j).natDegree) :
    (Matrix.of fun i j : Fin k ↦ (⇑polyEuler)^[i] (p j)).det ≠ 0 := by
  classical
  have hcoeff : (Matrix.of fun i j : Fin k ↦ (⇑polyEuler)^[i] (p j)).det.coeff
      (∑ j, (p j).natDegree) = (∏ j, (p j).leadingCoeff) *
        (Matrix.vandermonde fun j ↦ ((p j).natDegree : ℚ)).transpose.det := by
    rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [Units.smul_def, Units.smul_def, AddMonoidAlgebra.coeff_smul_apply, mul_smul_comm]
    congr 1
    simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.vandermonde_apply]
    rw [coeff_prod_of_natDegree_le' _ _ _ (fun i _ ↦ natDegree_polyEuler_iterate_le _ _),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [coeff_polyEuler_iterate, Polynomial.leadingCoeff, mul_comm]
  intro h
  rw [h, Polynomial.coeff_zero] at hcoeff
  have h1 : (∏ j, (p j).leadingCoeff) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ ↦ Polynomial.leadingCoeff_ne_zero.mpr (hp j)
  have h2 : (Matrix.vandermonde fun j ↦ ((p j).natDegree : ℚ)).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
    exact Nat.cast_injective.comp hd
  exact mul_ne_zero h1 h2 hcoeff.symm

/-- A linearly independent family of `k` polynomials spans `k` non-zero polynomials of pairwise
distinct degrees. -/
lemma exists_distinct_natDegree {k : ℕ} (ψ : Fin k → Polynomial ℚ) (hψ : LinearIndependent ℚ ψ) :
    ∃ p : Fin k → Polynomial ℚ, (∀ j, p j ≠ 0) ∧ Function.Injective (fun j ↦ (p j).natDegree) ∧
      ∀ j, p j ∈ Submodule.span ℚ (Set.range ψ) := by
  classical
  set W := Submodule.span ℚ (Set.range ψ) with hW
  have hdeg : ∀ p ∈ W, p.natDegree ≤ ∑ j, (ψ j).natDegree := by
    intro p hp
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hp
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ ↦ ?_
    exact (Polynomial.natDegree_smul_le _ _).trans
      (Finset.single_le_sum (f := fun j ↦ (ψ j).natDegree) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ j))
  set T := (Finset.range (∑ j, (ψ j).natDegree + 1)).filter
    (fun d ↦ ∃ p ∈ W, p ≠ 0 ∧ p.natDegree = d) with hT
  let f : W →ₗ[ℚ] (T → ℚ) := LinearMap.pi fun d ↦ (Polynomial.lcoeff ℚ (d : ℕ)).comp W.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro p hp
    by_contra hp0
    have hp0' : (p : Polynomial ℚ) ≠ 0 := fun h ↦ hp0 (Subtype.ext h)
    have hmem : (p : Polynomial ℚ).natDegree ∈ T := by
      rw [hT, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (hdeg p p.2), p, p.2, hp0', rfl⟩
    have := congrFun (LinearMap.mem_ker.mp hp) ⟨_, hmem⟩
    simp only [f, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      Polynomial.lcoeff_apply, Pi.zero_apply] at this
    exact hp0' (Polynomial.leadingCoeff_eq_zero.mp this)
  have hcard : k ≤ Fintype.card T := by
    have := LinearMap.finrank_le_finrank_of_injective hf
    rwa [finrank_span_eq_card hψ, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
  have hT' : ∀ j : Fin k, ∃ p ∈ W, p ≠ 0 ∧
      p.natDegree = ((Fintype.equivFin T).symm (Fin.castLE hcard j) : ℕ) := by
    intro j
    have := ((Fintype.equivFin T).symm (Fin.castLE hcard j)).2
    exact (Finset.mem_filter.mp this).2
  choose p hpW hp0 hpd using hT'
  refine ⟨p, hp0, fun i j hij ↦ ?_, hpW⟩
  simp only [hpd] at hij
  exact Fin.castLE_injective hcard ((Fintype.equivFin T).symm.injective (Subtype.ext hij))

/-- `det((s d/ds)^i ψ_j) ≠ 0` if the `ψ_j` are linearly independent. -/
lemma det_polyEuler_ne_zero {k : ℕ} (ψ : Fin k → Polynomial ℚ) (hψ : LinearIndependent ℚ ψ) :
    (Matrix.of fun i j : Fin k ↦ (⇑polyEuler)^[i] (ψ j)).det ≠ 0 := by
  obtain ⟨p, hp0, hpd, hpspan⟩ := exists_distinct_natDegree ψ hψ
  choose A hA using fun j ↦ (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hpspan j)
  have hM : (Matrix.of fun i j : Fin k ↦ (⇑polyEuler)^[i] (p j)) =
      (Matrix.of fun i j : Fin k ↦ (⇑polyEuler)^[i] (ψ j)) *
        Matrix.of fun l j ↦ Polynomial.C (A j l) := by
    refine Matrix.ext fun i j ↦ ?_
    simp only [Matrix.of_apply, Matrix.mul_apply]
    rw [← hA j, ← pow_apply_eq_iterate polyEuler, map_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_smul, pow_apply_eq_iterate, Polynomial.smul_eq_C_mul, mul_comm]
  intro h
  apply det_polyEuler_ne_zero_of_injective p hp0 hpd
  rw [hM, Matrix.det_mul, h, zero_mul]

/-! ### Back to divided derivatives -/

/-- A determinant vanishes if it vanishes whenever each row is taken from a generating set. -/
lemma det_eq_zero_of_mem_span {A : Type*} [CommRing A] {k : ℕ} (s : Fin k → Set (Fin k → A))
    (h : ∀ v : Fin k → Fin k → A, (∀ i, v i ∈ s i) → (Matrix.of v).det = 0)
    (M : Matrix (Fin k) (Fin k) A) (hM : ∀ i, M i ∈ Submodule.span A (s i)) : M.det = 0 := by
  classical
  suffices H : ∀ T : Finset (Fin k), ∀ v : Fin k → Fin k → A,
      (∀ i ∈ T, v i ∈ Submodule.span A (s i)) → (∀ i ∉ T, v i ∈ s i) →
      Matrix.detRowAlternating v = 0 from
    H Finset.univ M (fun i _ ↦ hM i) (fun i hi ↦ absurd (Finset.mem_univ i) hi)
  intro T
  induction T using Finset.induction_on with
  | empty => exact fun v _ hv ↦ h v fun i ↦ hv i (Finset.notMem_empty i)
  | insert a T ha ih =>
    intro v hT hv
    have key : ∀ x ∈ Submodule.span A (s a),
        Matrix.detRowAlternating (Function.update v a x) = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        refine ih _ (fun i hi ↦ ?_) (fun i hi ↦ ?_)
        · rw [Function.update_of_ne (by rintro rfl; exact ha hi)]
          exact hT i (Finset.mem_insert_of_mem hi)
        · by_cases hia : i = a
          · subst hia
            rwa [Function.update_self]
          · rw [Function.update_of_ne hia]
            exact hv i (by simp [hia, hi])
      | zero => exact AlternatingMap.map_update_zero _ _ _
      | add x y _ _ hx hy => rw [AlternatingMap.map_update_add, hx, hy, add_zero]
      | smul c x _ hx => rw [AlternatingMap.map_update_smul, hx, smul_zero]
    have := key (v a) (hT a (Finset.mem_insert_self a T))
    rwa [Function.update_eq_self] at this

lemma pderiv_hasseDeriv [Fintype τ] (t : τ) (β : τ →₀ ℕ) (P : MvPolynomial τ ℚ) :
    pderiv t (hasseDeriv β P) =
      ((β t + 1 : ℕ) : MvPolynomial τ ℚ) * hasseDeriv (β + Finsupp.single t 1) P := by
  classical
  have h1 : ∀ F : MvPolynomial τ ℚ, pderiv t F = hasseDeriv (Finsupp.single t 1) F := by
    intro F
    induction F using MvPolynomial.induction_on' with
    | add F G hF hG => rw [hasseDeriv_add, map_add, hF, hG]
    | monomial j a =>
      rw [hasseDeriv_monomial, pderiv_monomial, Finsupp.prod_single_index (by simp),
        Nat.choose_one_right, nsmul_eq_mul, mul_comm]
  rw [h1, hasseDeriv_hasseDeriv, map_natCast]
  congr 3
  rw [Finset.prod_eq_single t (fun v _ hv ↦ by simp [Finsupp.single_eq_of_ne hv])
    (by simp)]
  simp

/-- The row `(E^i φ_j)_j` lies in the span of the rows `(Δ_β φ_j)_j` with `|β| ≤ i`. -/
lemma eulerOp_iterate_mem_span [Fintype τ] (w : τ → ℕ) {k : ℕ} (φ : Fin k → MvPolynomial τ ℚ)
    (i : ℕ) : (fun j ↦ (⇑(eulerOp w))^[i] (φ j)) ∈ Submodule.span (MvPolynomial τ ℚ)
      {r | ∃ β : τ →₀ ℕ, β.degree ≤ i ∧ r = fun j ↦ hasseDeriv β (φ j)} := by
  classical
  set V : ℕ → Submodule (MvPolynomial τ ℚ) (Fin k → MvPolynomial τ ℚ) := fun i ↦
    Submodule.span (MvPolynomial τ ℚ)
      {r | ∃ β : τ →₀ ℕ, β.degree ≤ i ∧ r = fun j ↦ hasseDeriv β (φ j)} with hV
  have hmono : ∀ i, V i ≤ V (i + 1) := fun i ↦ Submodule.span_mono fun r ⟨β, hβ, hr⟩ ↦
    ⟨β, by omega, hr⟩
  have hstep : ∀ i, ∀ v ∈ V i, (fun j ↦ eulerOp w (v j)) ∈ V (i + 1) := by
    intro i v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨β, hβ, rfl⟩ := hv
      have : (fun j ↦ eulerOp w (hasseDeriv β (φ j))) = ∑ t, (C (w t : ℚ) * X t *
          ((β t + 1 : ℕ) : MvPolynomial τ ℚ)) • fun j ↦ hasseDeriv (β + Finsupp.single t 1) (φ j) := by
        funext j
        rw [eulerOp_apply, Finset.sum_apply]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [pderiv_hasseDeriv, Pi.smul_apply, smul_eq_mul]
        ring
      rw [this]
      refine Submodule.sum_mem _ fun t _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine ⟨β + Finsupp.single t 1, ?_, rfl⟩
      rw [map_add, Finsupp.degree_single]
      omega
    | zero =>
      convert (V (i + 1)).zero_mem using 1
      funext j
      simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      funext j
      simp
    | smul a x hx hx' =>
      have : (fun j ↦ eulerOp w ((a • x) j)) = eulerOp w a • x + a • fun j ↦ eulerOp w (x j) := by
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, Derivation.leibniz, Pi.add_apply]
        ring
      rw [this]
      exact add_mem (Submodule.smul_mem _ _ (hmono i hx)) (Submodule.smul_mem _ _ hx')
  induction i with
  | zero =>
    refine Submodule.subset_span ⟨0, by simp, ?_⟩
    funext j
    simp
  | succ i ih =>
    have := hstep i _ ih
    simp only [Function.iterate_succ_apply']
    exact this

end GeneralizedWronskian

/-- **Generalized Wronskians** ([schmidt1980], Chapter V, Lemma 9A): if the polynomials
`φ₁, …, φ_k` are linearly independent over `ℚ`, there are divided derivatives `Δ_i` of order at
most `i - 1` (`i = 1, …, k`) such that `det(Δ_i φ_j) ≠ 0`. -/
theorem exists_wronskian_ne_zero {τ : Type*} [Fintype τ] {k : ℕ}
    (φ : Fin k → MvPolynomial τ ℚ) (hφ : LinearIndependent ℚ φ) :
    ∃ D : Fin k → τ →₀ ℕ, (∀ i, (D i).degree ≤ i) ∧
      (Matrix.of fun i j ↦ hasseDeriv (D i) (φ j)).det ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set N := (∑ j, (φ j).totalDegree) + 1 with hN
  obtain ⟨w, hw⟩ := exists_kronecker_weights (τ := τ) N
  have hbound : ∀ p ∈ Submodule.span ℚ (Set.range φ), ∀ α ∈ p.support, ∀ t, α t < N := by
    intro p hp α hα t
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hp
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (support_sum hα)
    have h1 : α t ≤ α.degree := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ t)
    have h2 : α.degree ≤ (φ j).totalDegree := le_totalDegree (support_smul hj)
    have h3 : (φ j).totalDegree ≤ ∑ j, (φ j).totalDegree :=
      Finset.single_le_sum (f := fun j ↦ (φ j).totalDegree) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ j)
    omega
  have hψ : LinearIndependent ℚ (fun j ↦ kron w (φ j)) := by
    refine hφ.map (f := (kron w).toLinearMap) ?_
    rw [Submodule.disjoint_def]
    intro p hp hker
    exact eq_zero_of_kron_eq_zero hw p (hbound p hp) hker
  have h3 := det_polyEuler_ne_zero _ hψ
  have h4 : (Matrix.of fun i j : Fin k ↦ (⇑(eulerOp w))^[i] (φ j)).det = 0 := by
    refine det_eq_zero_of_mem_span (fun i : Fin k ↦ {r | ∃ β : τ →₀ ℕ, β.degree ≤ i ∧
      r = fun j ↦ hasseDeriv β (φ j)}) (fun v hv ↦ ?_) _ (fun i ↦ eulerOp_iterate_mem_span w φ i)
    choose β hβ hv using hv
    have hv' : v = fun i j ↦ hasseDeriv (β i) (φ j) := funext hv
    rw [hv']
    exact hcon β hβ
  apply h3
  have hit : ∀ (i : ℕ) (p : MvPolynomial τ ℚ),
      kron w ((⇑(eulerOp w))^[i] p) = (⇑polyEuler)^[i] (kron w p) := by
    intro i
    induction i with
    | zero => intro p; rfl
    | succ i ih =>
      intro p
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', kron_eulerOp, ih]
  have h5 : kron w (Matrix.of fun i j : Fin k ↦ (⇑(eulerOp w))^[i] (φ j)).det =
      (Matrix.of fun i j : Fin k ↦ (⇑polyEuler)^[i] (kron w (φ j))).det := by
    rw [AlgHom.map_det]
    congr 1
    ext i j
    simp [hit]
  rw [← h5, h4, map_zero]

end Schmidt
