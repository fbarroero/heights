module

public import Heights.SubspaceTheorem.Index

/-!
# Taylor's formula for divided derivatives and block-linear substitutions

This file contains the algebraic tools on divided derivatives needed in Step 2 of the proof of the
Subspace Theorem ([evertse1993], Section 3.4):

* `Schmidt.coeff_aeval_C_add_X`: Taylor's formula, `P(y + X) = ∑ κ, P_κ(y) X ^ κ`;
* `Schmidt.hasseDeriv_hasseDeriv`: `(P_i)_j` is a multiple of `P_{i + j}`;
* `Schmidt.IsBlockHomogeneous.aeval_blockLin`: a substitution which is linear in each block of
  variables preserves block homogeneity;
* `Schmidt.exists_int_point`: if a divided derivative `P_i` does not vanish at a rational point
  of the form `(G₁ y₁, …, Gₘ yₘ)`, then a divided derivative `P_{i'}` of slightly larger order does
  not vanish at an integer point `(G₁ z₁, …, Gₘ zₘ)` with `z` small;
* `Schmidt.eval_linExpand`: the value of `linExpand L R` at `(L x₁, …, L xₘ)` is `R(x)`;
* `Schmidt.abs_eval_le_of_block`: a trivial upper bound for the value of a polynomial.
-/

@[expose] public section

namespace Schmidt

open MvPolynomial Matrix

section Taylor

variable {σ R : Type*} [CommSemiring R]

/-- The coefficients of `∏ p, (y_p + X_p) ^ j_p`. -/
theorem coeff_prod_C_add_X_pow [Fintype σ] (y : σ → R) (j κ : σ →₀ ℕ) :
    (∏ p, (C (y p) + X p : MvPolynomial σ R) ^ j p).coeff κ =
      ∏ p, ((j p).choose (κ p) : R) * y p ^ (j p - κ p) := by
  classical
  have h1 : ∀ p, (C (y p) + X p : MvPolynomial σ R) ^ j p =
      ∑ t ∈ Finset.range (j p + 1),
        monomial (Finsupp.single p t) (((j p).choose t : R) * y p ^ (j p - t)) := by
    intro p
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [X_pow_eq_monomial, ← C_pow, ← C_eq_natCast, mul_assoc, ← C_mul, mul_comm,
      C_mul_monomial, mul_one, mul_comm]
  simp_rw [h1]
  rw [Finset.prod_univ_sum]
  simp_rw [← monomial_sum_prod]
  rw [coeff_sum]
  simp_rw [coeff_monomial]
  by_cases hκ : ∀ p, κ p ≤ j p
  · rw [Finset.sum_eq_single (⇑κ)]
    · rw [ite_eq_left (Finsupp.univ_sum_single κ)]
    · intro t _ ht
      rw [ite_eq_right]
      intro h
      apply ht
      rw [← h]
      funext p
      simp [Finsupp.single_apply]
    · intro h
      exact absurd (Fintype.mem_piFinset.mpr fun p ↦ Finset.mem_range.mpr
        (Nat.lt_succ_of_le (hκ p))) h
  · push Not at hκ
    obtain ⟨p, hp⟩ := hκ
    rw [Finset.prod_eq_zero (Finset.mem_univ p) (by rw [Nat.choose_eq_zero_of_lt hp]; simp)]
    refine Finset.sum_eq_zero fun t ht ↦ ?_
    rw [ite_eq_right]
    intro h
    have h2 := Finset.mem_range.mp (Fintype.mem_piFinset.mp ht p)
    have h3 : κ p = t p := by
      rw [← h]
      simp [Finsupp.single_apply]
    omega

/-- **Taylor's formula** for divided derivatives: the coefficient of `X ^ κ` in `F(y + X)` is the
value at `y` of the divided derivative `F_κ`. -/
theorem coeff_aeval_C_add_X [Fintype σ] (y : σ → R) (κ : σ →₀ ℕ) (F : MvPolynomial σ R) :
    (aeval (fun p ↦ C (y p) + X p) F : MvPolynomial σ R).coeff κ =
      MvPolynomial.eval y (hasseDeriv κ F) := by
  induction F using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, hasseDeriv_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
  | monomial j a =>
    rw [aeval_monomial, eval_hasseDeriv_monomial, Finsupp.prod_fintype _ _ (by simp),
      algebraMap_eq, coeff_C_mul, coeff_prod_C_add_X_pow, mul_comm]

/-- Taylor's formula: `F(x + w) = ∑ j, F_j(x) w ^ j`. -/
theorem aeval_algebraMap_add [Fintype σ] {B : Type*} [CommSemiring B] [Algebra R B] (x : σ → R)
    (w : σ → B) (F : MvPolynomial σ R) :
    aeval (fun p ↦ algebraMap R B (x p) + w p) F =
      ∑ j ∈ (aeval (fun p ↦ C (x p) + X p) F : MvPolynomial σ R).support,
        algebraMap R B (MvPolynomial.eval x (hasseDeriv j F)) * j.prod fun p k ↦ w p ^ k := by
  set G : MvPolynomial σ R := aeval (fun p ↦ C (x p) + X p) F with hG
  have h1 : aeval w G = aeval (fun p ↦ algebraMap R B (x p) + w p) F := by
    rw [hG, comp_aeval_apply]
    simp
  rw [← h1]
  conv_lhs => rw [as_sum G]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [aeval_monomial, hG, coeff_aeval_C_add_X]

/-- The composition of two divided derivatives: `(P_i)_j = (i + j choose i) P_{i + j}`. -/
theorem hasseDeriv_hasseDeriv [Fintype σ] (i j : σ →₀ ℕ) (P : MvPolynomial σ R) :
    hasseDeriv j (hasseDeriv i P) =
      C ((∏ v, (i v + j v).choose (i v) : ℕ) : R) * hasseDeriv (i + j) P := by
  ext k
  rw [coeff_hasseDeriv, coeff_hasseDeriv, coeff_C_mul, coeff_hasseDeriv,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp)]
  have hk : k + j + i = k + (i + j) := by rw [add_assoc, add_comm j i]
  rw [hk, smul_smul, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 2
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  simp only [Finsupp.add_apply]
  have h := Nat.choose_mul (n := k v + (i v + j v)) (k := i v + j v) (s := i v)
    (Nat.le_add_right _ _)
  have h1 : k v + (i v + j v) - i v = k v + j v := by omega
  have h2 : i v + j v - i v = j v := by omega
  rw [h1, h2] at h
  rw [mul_comm ((i v + j v).choose (i v)), h, mul_comm]
  congr 2
  omega

end Taylor

section Block

variable {m : ℕ} {ι : Type*} [Fintype ι]

/-- The linear form `∑ k, M_h l k X_{h k}` in the block of variables `X_h`, attached to the
variable `(h, l)` and to the matrices `M₁, …, Mₘ`. -/
noncomputable def blockLin {A : Type*} [CommSemiring A] (M : Fin m → Matrix ι ι A)
    (p : Fin m × ι) : MvPolynomial (Fin m × ι) A :=
  ∑ k, C (M p.1 p.2 k) * X (p.1, k)

lemma linExpand_eq_aeval [DecidableEq ι] (L : Matrix ι ι ℝ) (P : MvPolynomial (Fin m × ι) ℤ) :
    linExpand L P = aeval (blockLin fun _ ↦ L⁻¹) P := rfl

/-- The weight of a monomial with respect to the block `h` is its degree in the variables of this
block. -/
lemma weight_block (h : Fin m) (j : Fin m × ι →₀ ℕ) :
    Finsupp.weight (fun p : Fin m × ι ↦ if p.1 = h then 1 else 0) j = ∑ k, j (h, k) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type,
    Finset.sum_eq_single h (fun b _ hb ↦ by simp [hb]) (by simp)]
  simp

lemma IsBlockHomogeneous.sum_eq {A : Type*} [CommSemiring A] {F : MvPolynomial (Fin m × ι) A}
    {d : Fin m → ℕ} (hF : IsBlockHomogeneous F d) {j : Fin m × ι →₀ ℕ} (hj : F.coeff j ≠ 0)
    (h : Fin m) : ∑ k, j (h, k) = d h := by
  rw [← weight_block]
  exact hF h hj

lemma IsBlockHomogeneous.degreeOf_le {A : Type*} [CommSemiring A]
    {F : MvPolynomial (Fin m × ι) A} {d : Fin m → ℕ} (hF : IsBlockHomogeneous F d) (h : Fin m)
    (k : ι) : F.degreeOf (h, k) ≤ d h := by
  refine degreeOf_le_iff.mpr fun j hj ↦ ?_
  rw [← hF.sum_eq (mem_support_iff.mp hj) h]
  exact Finset.single_le_sum (f := fun k ↦ j (h, k)) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k)

/-- The divided derivative `P_i` of a block homogeneous polynomial is block homogeneous. -/
lemma IsBlockHomogeneous.hasseDeriv {A : Type*} [CommSemiring A]
    {P : MvPolynomial (Fin m × ι) A} {d : Fin m → ℕ} (hP : IsBlockHomogeneous P d)
    (i : Fin m × ι →₀ ℕ) :
    IsBlockHomogeneous (hasseDeriv i P) fun h ↦ d h - ∑ k, i (h, k) := by
  intro h k hk
  rw [coeff_hasseDeriv] at hk
  have h0 : P.coeff (k + i) ≠ 0 := fun h0 ↦ hk (by rw [h0, smul_zero])
  have h1 := hP.sum_eq h0 h
  rw [weight_block]
  simp only [Finsupp.add_apply, Finset.sum_add_distrib] at h1
  show _ = d h - ∑ k, i (h, k)
  omega

lemma isWeightedHomogeneous_blockLin {A : Type*} [CommSemiring A] (M : Fin m → Matrix ι ι A)
    (h : Fin m) (p : Fin m × ι) :
    IsWeightedHomogeneous (fun p : Fin m × ι ↦ if p.1 = h then 1 else 0) (blockLin M p)
      (if p.1 = h then 1 else 0) :=
  IsWeightedHomogeneous.sum _ _ _ fun k _ ↦ (isWeightedHomogeneous_X _ _ (p.1, k)).C_mul _

lemma isWeightedHomogeneous_prod_blockLin {A : Type*} [CommSemiring A]
    (M : Fin m → Matrix ι ι A) (h : Fin m) (j : Fin m × ι →₀ ℕ) :
    IsWeightedHomogeneous (fun p : Fin m × ι ↦ if p.1 = h then 1 else 0)
      (j.prod fun p k ↦ blockLin M p ^ k) (∑ k, j (h, k)) := by
  rw [Finsupp.prod_fintype _ _ (by simp), ← weight_block h j, Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (by simp)]
  exact IsWeightedHomogeneous.prod _ _ _ fun p _ ↦ (isWeightedHomogeneous_blockLin M h p).pow _

/-- A substitution which is linear in each block of variables preserves block homogeneity. -/
lemma IsBlockHomogeneous.aeval_blockLin {A' A : Type*} [CommSemiring A'] [CommSemiring A]
    [Algebra A' A] {R : MvPolynomial (Fin m × ι) A'} {d : Fin m → ℕ}
    (hR : IsBlockHomogeneous R d) (M : Fin m → Matrix ι ι A) :
    IsBlockHomogeneous (aeval (blockLin M) R) d := by
  intro h
  have h1 : aeval (blockLin M) R =
      ∑ j ∈ R.support, aeval (blockLin M) (monomial j (R.coeff j)) := by
    conv_lhs => rw [as_sum R]
    rw [map_sum]
  rw [h1]
  refine IsWeightedHomogeneous.sum _ _ _ fun j hj ↦ ?_
  rw [aeval_monomial, MvPolynomial.algebraMap_apply, ← hR.sum_eq (mem_support_iff.mp hj) h]
  exact (isWeightedHomogeneous_prod_blockLin M h j).C_mul _

/-- If the divided derivative `P_i` of the block homogeneous polynomial `P` does not vanish at the
rational point `(G₁ y₁, …, Gₘ yₘ)`, then for every `B > 0` there are an integer point `z` with
`|z_{h k}| ≤ B` and a multi-index `i'` with `(i' / d) ≤ (i / d) + m n / B` such that `P_{i'}` does
not vanish at the integer point `(G₁ z₁, …, Gₘ zₘ)`. This follows from
`exists_hasseDeriv_eval_ne_zero` applied to `P_i(G₁ Y₁, …, Gₘ Yₘ)` and from Taylor's formula. -/
theorem exists_int_point (P : MvPolynomial (Fin m × ι) ℤ) (d : Fin m → ℕ)
    (hd : ∀ h, 0 < d h) (hP : IsBlockHomogeneous P d) (G : Fin m → Matrix ι ι ℤ)
    (i : Fin m × ι →₀ ℕ) (y : Fin m × ι → ℚ)
    (hne : MvPolynomial.eval (fun p ↦ ∑ k, (G p.1 p.2 k : ℚ) * y (p.1, k))
      (map (Int.castRingHom ℚ) (hasseDeriv i P)) ≠ 0) {B : ℝ} (hB : 0 < B) :
    ∃ (z : Fin m × ι → ℤ) (i' : Fin m × ι →₀ ℕ), (∀ p, |(z p : ℝ)| ≤ B) ∧
      blockWeight d i' ≤ blockWeight d i + m * (Fintype.card ι / B) ∧
      MvPolynomial.eval (fun p ↦ ∑ k, G p.1 p.2 k * z (p.1, k)) (hasseDeriv i' P) ≠ 0 := by
  classical
  set R := hasseDeriv i P with hR
  set f : MvPolynomial (Fin m × ι) ℤ := aeval (blockLin G) R with hf
  have hfhom := (hP.hasseDeriv i).aeval_blockLin G
  have hf0 : f ≠ 0 := by
    intro h0
    apply hne
    have h1 : aeval y f = aeval (fun p ↦ ∑ k, (G p.1 p.2 k : ℚ) * y (p.1, k)) R := by
      have h2 : (fun p ↦ aeval y (blockLin G p)) =
          fun p ↦ ∑ k, (G p.1 p.2 k : ℚ) * y (p.1, k) := by
        funext p
        simp [blockLin]
      rw [hf, comp_aeval_apply, h2]
    rw [eval_map, ← algebraMap_int_eq, ← aeval_def, ← h1, h0, map_zero]
  have hdeg : ∀ v : Fin m × ι, f.degreeOf v ≤ d v.1 := fun v ↦
    (hfhom.degreeOf_le v.1 v.2).trans (Nat.sub_le _ _)
  obtain ⟨z, κ, hz, hκ, hzne⟩ := exists_hasseDeriv_eval_ne_zero f hf0 (fun v ↦ d v.1) hdeg
    (fun _ ↦ B) (fun _ ↦ hB)
  set x' : Fin m × ι → ℤ := fun p ↦ ∑ k, G p.1 p.2 k * z (p.1, k) with hx'
  have hT : (aeval (fun p ↦ C (z p) + X p) f : MvPolynomial (Fin m × ι) ℤ) =
      ∑ j ∈ (aeval (fun p ↦ C (x' p) + X p) R : MvPolynomial (Fin m × ι) ℤ).support,
        C (MvPolynomial.eval x' (hasseDeriv j R)) * j.prod fun p k ↦ blockLin G p ^ k := by
    rw [hf, comp_aeval_apply]
    have h2 : (fun p ↦ aeval (fun p ↦ C (z p) + X p) (blockLin G p)) =
        fun p ↦ algebraMap ℤ (MvPolynomial (Fin m × ι) ℤ) (x' p) + blockLin G p := by
      funext p
      simp [blockLin, hx', mul_add, Finset.sum_add_distrib]
    rw [h2, aeval_algebraMap_add]
    rfl
  have hc : (aeval (fun p ↦ C (z p) + X p) f : MvPolynomial (Fin m × ι) ℤ).coeff κ ≠ 0 := by
    rw [coeff_aeval_C_add_X]
    simpa using hzne
  rw [hT, coeff_sum] at hc
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  rw [coeff_C_mul] at hj
  have hj1 : MvPolynomial.eval x' (hasseDeriv j R) ≠ 0 := left_ne_zero_of_mul hj
  have hj2 := right_ne_zero_of_mul hj
  have hblock : ∀ h, ∑ k, κ (h, k) = ∑ k, j (h, k) := fun h ↦ by
    rw [← weight_block h κ]
    exact isWeightedHomogeneous_prod_blockLin G h j hj2
  refine ⟨z, i + j, hz, ?_, ?_⟩
  · have hjle : ∀ h, (∑ k, (j (h, k) : ℝ)) / d h ≤ Fintype.card ι / B := fun h ↦ by
      have hdh : (0 : ℝ) < d h := by exact_mod_cast hd h
      have h3 : (∑ k, (j (h, k) : ℝ)) = ∑ k, (κ (h, k) : ℝ) := by exact_mod_cast (hblock h).symm
      rw [h3, div_le_iff₀ hdh]
      calc ∑ k, (κ (h, k) : ℝ) ≤ ∑ _k : ι, (d h : ℝ) / B :=
            Finset.sum_le_sum fun k _ ↦ hκ (h, k)
        _ = Fintype.card ι / B * d h := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
    calc blockWeight d (i + j) = blockWeight d i + ∑ h, (∑ k, (j (h, k) : ℝ)) / d h := by
          simp only [blockWeight, Finsupp.add_apply, Nat.cast_add, Finset.sum_add_distrib,
            add_div]
      _ ≤ blockWeight d i + ∑ _h : Fin m, (Fintype.card ι : ℝ) / B := by
          have := Finset.sum_le_sum fun h (_ : h ∈ Finset.univ) ↦ hjle h
          linarith
      _ = blockWeight d i + m * (Fintype.card ι / B) := by simp
  · rw [hR, hasseDeriv_hasseDeriv, map_mul] at hj1
    exact right_ne_zero_of_mul hj1

/-- The value of `linExpand L R` at the point `(L x₁, …, L xₘ)` is `R(x₁, …, xₘ)`. -/
theorem eval_linExpand [DecidableEq ι] (L : Matrix ι ι ℝ) (hL : L.det ≠ 0)
    (R : MvPolynomial (Fin m × ι) ℤ) (x : Fin m → ι → ℤ) :
    MvPolynomial.eval (fun p ↦ Schmidt.eval L (x p.1) p.2) (linExpand L R) =
      ((MvPolynomial.eval (fun p ↦ x p.1 p.2) R : ℤ) : ℝ) := by
  have h1 : (fun p : Fin m × ι ↦ ∑ k, L⁻¹ p.2 k * Schmidt.eval L (x p.1) k) =
      algebraMap ℤ ℝ ∘ fun p ↦ x p.1 p.2 := by
    funext p
    have h2 : L⁻¹ *ᵥ (L *ᵥ fun j ↦ (x p.1 j : ℝ)) = fun j ↦ (x p.1 j : ℝ) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hL),
        Matrix.one_mulVec]
    simpa [Schmidt.eval, Matrix.mulVec, dotProduct] using congrFun h2 p.2
  have h3 : (MvPolynomial.eval fun p : Fin m × ι ↦ Schmidt.eval L (x p.1) p.2).comp
      (algebraMap ℤ (MvPolynomial (Fin m × ι) ℝ)) = algebraMap ℤ ℝ := RingHom.ext_int _ _
  rw [linExpand, map_aeval, h3, ← aeval_eq_eval₂Hom]
  have h4 : (fun p : Fin m × ι ↦ MvPolynomial.eval (fun p : Fin m × ι ↦ Schmidt.eval L (x p.1) p.2)
      (∑ k, C (L⁻¹ p.2 k) * X (p.1, k))) =
      fun p ↦ ∑ k, L⁻¹ p.2 k * Schmidt.eval L (x p.1) k := by
    funext p
    simp
  rw [h4, h1, aeval_algebraMap_apply]
  simp [aeval_eq_eval]

/-- A trivial bound for the value of a polynomial: if every monomial of `F` has degree at most
`d h` in the block of variables `X_h` and every term of `F(U)` has absolute value at most `M`, then
`|F(U)| ≤ 2 ^ (n (d₁ + ⋯ + dₘ)) M`. -/
theorem abs_eval_le_of_block (F : MvPolynomial (Fin m × ι) ℝ) (d : Fin m → ℕ)
    (hF : ∀ j ∈ F.support, ∀ h, ∑ k, j (h, k) ≤ d h) (U : Fin m × ι → ℝ) {M : ℝ}
    (hM0 : 0 ≤ M)
    (hM : ∀ j ∈ F.support, |F.coeff j * ∏ p, U p ^ j p| ≤ M) :
    |MvPolynomial.eval U F| ≤ 2 ^ (Fintype.card ι * ∑ h, d h) * M := by
  classical
  have hcard : (F.support.card : ℝ) ≤ 2 ^ (Fintype.card ι * ∑ h, d h) := by
    have h1 : F.support.card ≤
        (Fintype.piFinset fun p : Fin m × ι ↦ Finset.range (d p.1 + 1)).card := by
      refine Finset.card_le_card_of_injOn (fun j ↦ ⇑j) (fun j hj ↦ ?_)
        (fun _ _ _ _ h ↦ DFunLike.coe_injective h)
      refine Fintype.mem_piFinset.mpr fun p ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le ?_)
      exact (Finset.single_le_sum (f := fun k ↦ j (p.1, k)) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ p.2)).trans (hF j hj p.1)
    have h2 : (Fintype.piFinset fun p : Fin m × ι ↦ Finset.range (d p.1 + 1)).card ≤
        2 ^ (Fintype.card ι * ∑ h, d h) := by
      rw [Fintype.card_piFinset, Fintype.prod_prod_type, Finset.mul_sum,
        ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod fun h _ ↦ ?_
      simp only [Finset.card_range, Finset.prod_const, Finset.card_univ]
      rw [pow_mul']
      exact Nat.pow_le_pow_left Nat.lt_two_pow_self _
    exact_mod_cast h1.trans h2
  rw [eval_eq']
  calc |∑ j ∈ F.support, F.coeff j * ∏ p, U p ^ j p|
      ≤ ∑ j ∈ F.support, |F.coeff j * ∏ p, U p ^ j p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ F.support, M := Finset.sum_le_sum hM
    _ = F.support.card * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (Fintype.card ι * ∑ h, d h) * M := by gcongr

end Block

end Schmidt
