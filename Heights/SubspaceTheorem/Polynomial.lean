module

public import Mathlib

/-!
# Divided derivatives of multivariate polynomials and a non-vanishing lemma

We define the divided (Hasse) derivatives `P_i = (1 / i!) ∂^i P` of a multivariate polynomial `P`
and we prove [evertse1993], Lemma 3.4.10 (a special case of [schmidt1980], Lemma 8A, p. 184):
a non-zero polynomial of degree at most `s_v` in the variable `X_v` has a divided derivative of
order at most `s_v / B_v` in `X_v` which does not vanish at some integer point `x` with
`|x_v| ≤ B_v`.
-/

@[expose] public section

namespace Schmidt

variable {σ R : Type*} [CommSemiring R]

/-- The divided derivative `P_i = (1 / i₁! ⋯ iᵣ!) (∂/∂X₁)^{i₁} ⋯ (∂/∂Xᵣ)^{iᵣ} P` (also known as
Hasse derivative) of the multivariate polynomial `P`: the monomial `X ^ j` is sent to
`(j choose i) X ^ (j - i)`, where `(j choose i)` is the product of the binomial coefficients
`(j_v choose i_v)`. -/
noncomputable def hasseDeriv (i : σ →₀ ℕ) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ j ∈ P.support, MvPolynomial.monomial (j - i) ((i.prod fun v k ↦ (j v).choose k) • P.coeff j)

section API

open MvPolynomial

/-- `hasseDeriv i P` as a `Finsupp.sum` over the coefficients of `P`. -/
theorem hasseDeriv_eq_sum (i : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasseDeriv i P = P.coeff.sum fun j a ↦
      monomial (j - i) ((i.prod fun v k ↦ (j v).choose k) • a) := by
  rw [sum_def, hasseDeriv]

/-- The divided derivative is additive. -/
theorem hasseDeriv_add (i : σ →₀ ℕ) (P Q : MvPolynomial σ R) :
    hasseDeriv i (P + Q) = hasseDeriv i P + hasseDeriv i Q := by
  simp only [hasseDeriv_eq_sum, AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (by simp) (by simp [smul_add])

/-- The divided derivative of a monomial: `X ^ j ↦ (j choose i) X ^ (j - i)`. -/
theorem hasseDeriv_monomial (i j : σ →₀ ℕ) (a : R) :
    hasseDeriv i (monomial j a) =
      monomial (j - i) ((i.prod fun v k ↦ (j v).choose k) • a) := by
  rw [hasseDeriv_eq_sum]
  exact Finsupp.sum_single_index (by simp)

/-- The divided derivative of order `0` is the identity. -/
@[simp]
theorem hasseDeriv_zero_left (P : MvPolynomial σ R) : hasseDeriv 0 P = P := by
  induction P using MvPolynomial.induction_on' with
  | monomial j a => simp [hasseDeriv_monomial]
  | add p q hp hq => rw [hasseDeriv_add, hp, hq]

/-- The value at `x` of the divided derivative of a monomial. -/
theorem eval_hasseDeriv_monomial [Fintype σ] (x : σ → R) (i j : σ →₀ ℕ) (a : R) :
    eval x (hasseDeriv i (monomial j a)) =
      (∏ v, ((j v).choose (i v) : R) * x v ^ (j v - i v)) * a := by
  rw [hasseDeriv_monomial, eval_monomial, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp), Finset.prod_mul_distrib]
  simp only [nsmul_eq_mul, Nat.cast_prod, Finsupp.tsub_apply]
  ring

/-- The image of a monomial under `MvPolynomial.finSuccEquiv`. -/
theorem finSuccEquiv_monomial {n : ℕ} (j : Fin (n + 1) →₀ ℕ) (a : R) :
    finSuccEquiv R n (monomial j a) = Polynomial.monomial (j 0) (monomial j.tail a) := by
  rw [finSuccEquiv_apply, coe_eval₂Hom, eval₂_monomial, Finsupp.prod_fintype _ _ (by simp),
    Fin.prod_univ_succ, ← Polynomial.C_mul_X_pow_eq_monomial, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [RingHom.coe_comp, Function.comp_apply, Fin.cases_zero, Fin.cases_succ,
    Finsupp.tail_apply, map_mul, map_prod, map_pow]
  ring

/-- Compatibility of the divided derivative with the splitting of the first variable: the value
at `(x₀, x)` of the divided derivative of order `(i₀, i)` of `P` is the value at `x` of the
divided derivative of order `i` of `Q`, where `Q` is the one-variable divided derivative of order
`i₀` of `P` with respect to `X 0`, evaluated at `X 0 = x₀`. -/
theorem eval_hasseDeriv_cons {n : ℕ} (x₀ : R) (x : Fin n → R) (i₀ : ℕ) (i : Fin n →₀ ℕ)
    (P : MvPolynomial (Fin (n + 1)) R) :
    eval (Fin.cons x₀ x : Fin (n + 1) → R) (hasseDeriv (i.cons i₀) P) =
      eval x (hasseDeriv i
        (Polynomial.eval (C x₀) (Polynomial.hasseDeriv i₀ (finSuccEquiv R n P)))) := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [hasseDeriv_add, map_add, hp, hq, Polynomial.eval_add]
  | monomial j a =>
    have key : (((j 0).choose i₀ : MvPolynomial (Fin n) R) * monomial j.tail a) *
        C x₀ ^ (j 0 - i₀) = monomial j.tail (((j 0).choose i₀ : R) * x₀ ^ (j 0 - i₀) * a) := by
      rw [← C_eq_natCast, ← C_pow, C_mul_monomial, mul_comm, C_mul_monomial]
      congr 1
      ring
    rw [finSuccEquiv_monomial, Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial, key,
      eval_hasseDeriv_monomial, eval_hasseDeriv_monomial, Fin.prod_univ_succ]
    simp only [Finsupp.cons_zero, Finsupp.cons_succ, Fin.cons_zero, Fin.cons_succ,
      Finsupp.tail_apply]
    ring

/-- The divided derivative commutes with an injective renaming of the variables. -/
theorem hasseDeriv_rename {τ : Type*} {f : σ → τ} (hf : Function.Injective f) (i : σ →₀ ℕ)
    (P : MvPolynomial σ R) :
    hasseDeriv (i.mapDomain f) (rename f P) = rename f (hasseDeriv i P) := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [hasseDeriv_add, map_add, hp, hq]
  | monomial j a =>
    rw [rename_monomial, hasseDeriv_monomial, hasseDeriv_monomial, rename_monomial,
      Finsupp.mapDomain_tsub hf, Finsupp.prod_mapDomain_index_inj hf]
    simp only [Finsupp.mapDomain_apply_of_injective hf]

/-- The divided derivative commutes with scalar multiplication. -/
theorem hasseDeriv_smul (i : σ →₀ ℕ) (c : R) (P : MvPolynomial σ R) :
    hasseDeriv i (c • P) = c • hasseDeriv i P := by
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [hasseDeriv_add, smul_add, hp, hq]
  | monomial j a => simp only [smul_monomial, hasseDeriv_monomial, smul_comm c]

/-- The divided derivative `hasseDeriv i` as a linear map. -/
noncomputable def hasseDerivₗ (i : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R where
  toFun := hasseDeriv i
  map_add' := hasseDeriv_add i
  map_smul' := hasseDeriv_smul i

@[simp]
theorem hasseDerivₗ_apply (i : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasseDerivₗ i P = hasseDeriv i P := rfl

/-- The coefficients of the divided derivative:
`coeff k (P_i) = (k + i choose i) coeff (k + i) P`. -/
theorem coeff_hasseDeriv (i k : σ →₀ ℕ) (P : MvPolynomial σ R) :
    (hasseDeriv i P).coeff k = (i.prod fun v m ↦ (k v + m).choose m) • P.coeff (k + i) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [hasseDeriv_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, smul_add]
  | monomial j a =>
    rw [hasseDeriv_monomial, coeff_monomial, coeff_monomial]
    by_cases hj : j = k + i
    · subst hj
      simp [Finsupp.prod]
    · simp only [hj, ↓reduceIte, smul_zero]
      split_ifs with h
      · have hij : ¬ i ≤ j := fun hij ↦ hj (by rw [← h, tsub_add_cancel_of_le hij])
        obtain ⟨v, hv⟩ : ∃ v, j v < i v := by
          by_contra! hc
          exact hij hc
        have : (i.prod fun v k ↦ (j v).choose k) = 0 :=
          Finset.prod_eq_zero (i := v) (Finsupp.mem_support_iff.mpr (by omega))
            (Nat.choose_eq_zero_of_lt hv)
        rw [this, zero_smul]
      · rfl

/-- One-variable case of `exists_hasseDeriv_eval_ne_zero`. -/
theorem exists_polynomial_hasseDeriv_eval_ne_zero {A : Type*} [CommRing A] [IsDomain A]
    [CharZero A] (f : Polynomial A) (hf : f ≠ 0) (s : ℕ) (hs : f.natDegree ≤ s) (B : ℝ)
    (hB : 0 < B) :
    ∃ (x : ℤ) (i : ℕ), |(x : ℝ)| ≤ B ∧ (i : ℝ) ≤ s / B ∧
      (Polynomial.hasseDeriv i f).eval (x : A) ≠ 0 := by
  classical
  by_contra! h
  set a := ⌊B⌋₊ with ha
  set b := ⌊(s : ℝ) / B⌋₊ + 1 with hb
  have hmult : ∀ x ∈ Finset.Icc (-(a : ℤ)) a, b ≤ f.rootMultiplicity (x : A) := by
    intro x hx
    rw [Polynomial.le_rootMultiplicity_iff hf, Polynomial.X_sub_C_pow_dvd_iff,
      ← Polynomial.taylor_apply, Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.taylor_coeff]
    apply h
    · rw [Finset.mem_Icc] at hx
      have hxa : |(x : ℝ)| ≤ a := by
        rw [abs_le]
        exact_mod_cast hx
      exact hxa.trans (Nat.floor_le hB.le)
    · have hd' : d ≤ ⌊(s : ℝ) / B⌋₊ := Nat.lt_succ_iff.mp hd
      exact (Nat.le_floor_iff (by positivity)).mp hd'
  let T : Finset A := (Finset.Icc (-(a : ℤ)) a).map ⟨Int.cast, Int.cast_injective⟩
  have hle : b • T.val ≤ f.roots := by
    rw [Multiset.le_iff_count]
    intro y
    rw [Multiset.count_nsmul, Polynomial.count_roots]
    by_cases hy : y ∈ T
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      rw [Multiset.count_eq_one_of_mem T.nodup hy, mul_one]
      exact hmult x hx
    · rw [Multiset.count_eq_zero_of_notMem hy]
      simp
  have hcard := (Multiset.card_le_card hle).trans (f.card_roots'.trans hs)
  have h3 : ((a : ℤ) + 1 - (-(a : ℤ))).toNat = 2 * a + 1 := by omega
  rw [Multiset.card_nsmul, Finset.card_val, Finset.card_map, Int.card_Icc, h3] at hcard
  have h1 : B < a + 1 := Nat.lt_floor_add_one B
  have h2 : (s : ℝ) / B < b := by
    rw [hb]
    push_cast
    exact Nat.lt_floor_add_one _
  have h4 : (s : ℝ) < b * (2 * a + 1) := by
    calc (s : ℝ) = (s / B) * B := by field_simp
      _ < b * (2 * a + 1) :=
        mul_lt_mul'' h2 (by linarith [Nat.cast_nonneg (α := ℝ) a]) (by positivity) hB.le
  have h5 : (s : ℝ) < ((b * (2 * a + 1) : ℕ) : ℝ) := by
    push_cast
    exact h4
  exact absurd hcard (not_le.mpr (by exact_mod_cast h5))

/-- `exists_hasseDeriv_eval_ne_zero` for polynomials in the variables `Fin n`. -/
theorem exists_hasseDeriv_eval_ne_zero_fin {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (n : ℕ) (P : MvPolynomial (Fin n) R) (hP : P ≠ 0) (s : Fin n → ℕ)
    (hs : ∀ v, P.degreeOf v ≤ s v) (B : Fin n → ℝ) (hB : ∀ v, 0 < B v) :
    ∃ (x : Fin n → ℤ) (i : Fin n →₀ ℕ), (∀ v, |(x v : ℝ)| ≤ B v) ∧
      (∀ v, (i v : ℝ) ≤ s v / B v) ∧
      MvPolynomial.eval (fun v ↦ (x v : R)) (hasseDeriv i P) ≠ 0 := by
  induction n with
  | zero =>
    refine ⟨fun _ ↦ 0, 0, fun v ↦ v.elim0, fun v ↦ v.elim0, ?_⟩
    rw [hasseDeriv_zero_left]
    rw [eq_C_of_isEmpty P] at hP ⊢
    rw [eval_C]
    exact C_ne_zero.mp hP
  | succ n ih =>
    set f := finSuccEquiv R n P with hf
    have hf0 : f ≠ 0 := (map_ne_zero_iff _ (finSuccEquiv R n).injective).mpr hP
    have hdeg : f.natDegree ≤ s 0 := (natDegree_finSuccEquiv P).trans_le (hs 0)
    obtain ⟨x₀, i₀, hx₀, hi₀, hQ⟩ :=
      exists_polynomial_hasseDeriv_eval_ne_zero f hf0 (s 0) hdeg (B 0) (hB 0)
    have hcast : ((x₀ : ℤ) : MvPolynomial (Fin n) R) = C (x₀ : R) :=
      (map_intCast (C : R →+* MvPolynomial (Fin n) R) x₀).symm
    rw [hcast] at hQ
    set Q := Polynomial.eval (C (x₀ : R)) (Polynomial.hasseDeriv i₀ f) with hQdef
    have hQdeg : ∀ v, Q.degreeOf v ≤ s v.succ := by
      intro v
      rw [hQdef, Polynomial.eval_eq_sum_range]
      refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun m _ ↦ ?_)
      rw [Polynomial.hasseDeriv_coeff, ← C_eq_natCast, ← C_pow]
      refine (degreeOf_mul_le _ _ _).trans ?_
      rw [degreeOf_C, add_zero]
      refine (degreeOf_mul_le _ _ _).trans ?_
      rw [degreeOf_C, zero_add]
      exact (degreeOf_coeff_finSuccEquiv P v _).trans (hs v.succ)
    obtain ⟨x, i, hx, hi, hne⟩ := ih Q hQ (fun v ↦ s v.succ) hQdeg (fun v ↦ B v.succ)
      (fun v ↦ hB v.succ)
    refine ⟨Fin.cons x₀ x, i.cons i₀, ?_, ?_, ?_⟩
    · intro v
      refine Fin.cases ?_ (fun w ↦ ?_) v
      · simpa using hx₀
      · simpa using hx w
    · intro v
      refine Fin.cases ?_ (fun w ↦ ?_) v
      · simpa using hi₀
      · simpa using hi w
    · have hfun : (fun v ↦ ((Fin.cons x₀ x : Fin (n + 1) → ℤ) v : R)) =
          Fin.cons (x₀ : R) (fun v ↦ (x v : R)) := by
        funext v
        refine Fin.cases ?_ (fun w ↦ ?_) v <;> simp
      rw [hfun, eval_hasseDeriv_cons]
      exact hne

end API

/-- [evertse1993], Lemma 3.4.10. Let `P` be a non-zero polynomial of degree at most `s v` in the
variable `X v` and let `B v` be positive real numbers. Then there are an integer point `x` with
`|x v| ≤ B v` and a multi-index `i` with `i v ≤ s v / B v` such that the divided derivative
`P_i` does not vanish at `x`. -/
theorem exists_hasseDeriv_eval_ne_zero {σ R : Type*} [Fintype σ] [CommRing R] [IsDomain R]
    [CharZero R] (P : MvPolynomial σ R) (hP : P ≠ 0) (s : σ → ℕ)
    (hs : ∀ v, P.degreeOf v ≤ s v) (B : σ → ℝ) (hB : ∀ v, 0 < B v) :
    ∃ (x : σ → ℤ) (i : σ →₀ ℕ), (∀ v, |(x v : ℝ)| ≤ B v) ∧ (∀ v, (i v : ℝ) ≤ s v / B v) ∧
      MvPolynomial.eval (fun v ↦ (x v : R)) (hasseDeriv i P) ≠ 0 := by
  classical
  let e := Fintype.equivFin σ
  have hP' : MvPolynomial.rename e P ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.rename_injective e e.injective)).mpr hP
  have hs' : ∀ w, (MvPolynomial.rename e P).degreeOf w ≤ s (e.symm w) := by
    intro w
    have := MvPolynomial.degreeOf_rename_of_injective (p := P) e.injective (e.symm w)
    rw [e.apply_symm_apply] at this
    rw [this]
    exact hs _
  obtain ⟨x, i, hx, hi, hne⟩ := exists_hasseDeriv_eval_ne_zero_fin _ _ hP'
    (fun w ↦ s (e.symm w)) hs' (fun w ↦ B (e.symm w)) (fun w ↦ hB _)
  refine ⟨fun v ↦ x (e v), i.mapDomain e.symm, fun v ↦ ?_, fun v ↦ ?_, ?_⟩
  · simpa using hx (e v)
  · simpa [Finsupp.mapDomain_equiv_apply] using hi (e v)
  · have hi' : i = (i.mapDomain e.symm).mapDomain e := by
      rw [← Finsupp.mapDomain_comp]
      simp
    rw [hi', hasseDeriv_rename e.injective, MvPolynomial.eval_rename] at hne
    exact hne

end Schmidt
