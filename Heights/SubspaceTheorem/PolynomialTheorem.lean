module

public import Heights.SubspaceTheorem.HasseTaylor

/-!
# The polynomial theorem

We prove `Schmidt.polynomial_theorem` ([evertse1993], Proposition 3.4.3, [schmidt1980],
Chapter VI, Theorem 7A): the construction of the auxiliary polynomial in the proof of the
Subspace Theorem. The proof follows [schmidt1980], Chapter VI, §§4–7:

* `Schmidt.exists_coeff_ne_zero_of_hasseDeriv`: by the chain rule, the monomials of the expansion
  of `P_i` in the variables `U_{h k} = L_k(X_h)` are obtained from those of the expansion of `P` by
  lowering the degree in the block `U_h` by `i_{h 1} + ⋯ + i_{h n}`;
* `Schmidt.card_filter_far_mul_sq_le`: a second moment (Chebyshev) estimate showing that most
  block homogeneous monomials `U ^ j` satisfy `∑ h, j_{h k} / d_h ≈ m / n`
  ([schmidt1980], Chapter V, Lemma 4A);
* `Schmidt.exists_int_solution_of_house_le`: Siegel's lemma for linear systems with coefficients in
  the ring of integers of a number field, with integer solutions;
* `Schmidt.abs_coeff_aeval_hasseDeriv_le`: a trivial bound for the coefficients `d_{P, i}(j)`.

The coefficient bounds use a generic `ℓ¹`-norm `Schmidt.l1` of polynomials, with respect to any
subadditive and submultiplicative function on the coefficients (absolute value or house).
-/

@[expose] public section

namespace Schmidt

universe u v

open MvPolynomial Matrix Finset NumberField

/-! ### An `ℓ¹`-norm for polynomials -/

section L1

variable {σ R : Type*} [CommRing R]

/-- A subadditive and submultiplicative non-negative function on a ring, such as the absolute value
on `ℝ` or the house on a number field. -/
structure IsSubmulAbs (f : R → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ f a
  map_zero : f 0 = 0
  map_one_le : f 1 ≤ 1
  add_le : ∀ a b, f (a + b) ≤ f a + f b
  mul_le : ∀ a b, f (a * b) ≤ f a * f b

/-- The `ℓ¹`-norm of a polynomial with respect to `f`: the sum of the `f (coeff j)`. -/
noncomputable def l1 (f : R → ℝ) (F : MvPolynomial σ R) : ℝ := ∑ j ∈ F.support, f (F.coeff j)

variable {f : R → ℝ}

lemma IsSubmulAbs.l1_eq_sum_of_subset (hf : IsSubmulAbs f) {F : MvPolynomial σ R}
    {s : Finset (σ →₀ ℕ)} (hs : F.support ⊆ s) : l1 f F = ∑ j ∈ s, f (F.coeff j) :=
  Finset.sum_subset hs fun j _ hj ↦ by rw [notMem_support_iff.mp hj, hf.map_zero]

lemma IsSubmulAbs.l1_nonneg (hf : IsSubmulAbs f) (F : MvPolynomial σ R) : 0 ≤ l1 f F :=
  sum_nonneg fun _ _ ↦ hf.nonneg _

lemma IsSubmulAbs.le_l1 (hf : IsSubmulAbs f) (F : MvPolynomial σ R) (j : σ →₀ ℕ) :
    f (F.coeff j) ≤ l1 f F := by
  by_cases hj : j ∈ F.support
  · exact single_le_sum (f := fun j ↦ f (F.coeff j)) (fun _ _ ↦ hf.nonneg _) hj
  · rw [notMem_support_iff.mp hj, hf.map_zero]
    exact hf.l1_nonneg F

lemma IsSubmulAbs.l1_add_le (hf : IsSubmulAbs f) (F G : MvPolynomial σ R) :
    l1 f (F + G) ≤ l1 f F + l1 f G := by
  classical
  rw [hf.l1_eq_sum_of_subset (support_add (p := F) (q := G)),
    hf.l1_eq_sum_of_subset (subset_union_left (s₂ := G.support)),
    hf.l1_eq_sum_of_subset (subset_union_right (s₁ := F.support)), ← sum_add_distrib]
  refine sum_le_sum fun j _ ↦ ?_
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact hf.add_le _ _

lemma IsSubmulAbs.l1_sum_le (hf : IsSubmulAbs f) {α : Type*} (s : Finset α)
    (F : α → MvPolynomial σ R) : l1 f (∑ a ∈ s, F a) ≤ ∑ a ∈ s, l1 f (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (hf.l1_add_le _ _).trans (by linarith)

lemma IsSubmulAbs.l1_monomial (hf : IsSubmulAbs f) (x : σ →₀ ℕ) (a : R) :
    l1 f (monomial x a) = f a := by
  classical
  rw [hf.l1_eq_sum_of_subset support_monomial_subset, sum_singleton, coeff_monomial, ite_eq_left rfl]

lemma IsSubmulAbs.l1_mul_le (hf : IsSubmulAbs f) (F G : MvPolynomial σ R) :
    l1 f (F * G) ≤ l1 f F * l1 f G := by
  classical
  conv_lhs => rw [as_sum F, as_sum G, sum_mul_sum]
  refine (hf.l1_sum_le _ _).trans ?_
  rw [l1, l1, sum_mul_sum]
  refine sum_le_sum fun a _ ↦ (hf.l1_sum_le _ _).trans (sum_le_sum fun b _ ↦ ?_)
  rw [monomial_mul_monomial, hf.l1_monomial]
  exact hf.mul_le _ _

lemma IsSubmulAbs.l1_one_le (hf : IsSubmulAbs f) : l1 f (1 : MvPolynomial σ R) ≤ 1 := by
  rw [one_def, hf.l1_monomial]
  exact hf.map_one_le

lemma IsSubmulAbs.l1_prod_le (hf : IsSubmulAbs f) {α : Type*} (s : Finset α)
    (F : α → MvPolynomial σ R) : l1 f (∏ a ∈ s, F a) ≤ ∏ a ∈ s, l1 f (F a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hf.l1_one_le
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (hf.l1_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (hf.l1_nonneg _))

lemma IsSubmulAbs.l1_pow_le (hf : IsSubmulAbs f) (F : MvPolynomial σ R) (k : ℕ) :
    l1 f (F ^ k) ≤ l1 f F ^ k := by
  have := hf.l1_prod_le (Finset.range k) fun _ ↦ F
  simpa using this

lemma IsSubmulAbs.l1_blockLin_le {m : ℕ} {ι : Type*} [Fintype ι] (hf : IsSubmulAbs f)
    (M : Matrix ι ι R) (p : Fin m × ι) :
    l1 f (blockLin (fun _ ↦ M) p) ≤ ∑ k, f (M p.2 k) := by
  refine (hf.l1_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ ↦ ?_))
  rw [C_mul_X_eq_monomial, hf.l1_monomial]

/-- The `ℓ¹`-norm of `aeval (blockLin M) F`, for `F` with integer coefficients. -/
lemma IsSubmulAbs.l1_aeval_blockLin_le {m : ℕ} {ι : Type*} [Fintype ι] (hf : IsSubmulAbs f)
    (M : Matrix ι ι R) (F : MvPolynomial (Fin m × ι) ℤ) :
    l1 f (aeval (blockLin fun _ ↦ M) F) ≤
      ∑ y ∈ F.support, f (algebraMap ℤ R (F.coeff y)) * ∏ p, (∑ k, f (M p.2 k)) ^ y p := by
  conv_lhs => rw [as_sum F, map_sum]
  refine (hf.l1_sum_le _ _).trans (sum_le_sum fun y _ ↦ ?_)
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), MvPolynomial.algebraMap_apply]
  refine (hf.l1_mul_le _ _).trans ?_
  rw [← monomial_zero', hf.l1_monomial]
  refine mul_le_mul_of_nonneg_left ((hf.l1_prod_le _ _).trans ?_) (hf.nonneg _)
  refine prod_le_prod₀ (fun _ _ ↦ hf.l1_nonneg _) fun p _ ↦ ?_
  exact (hf.l1_pow_le _ _).trans (pow_le_pow_left₀ (hf.l1_nonneg _) (hf.l1_blockLin_le M p) _)

/-- The image under `f` of a coefficient of `(β U) ^ e` is at most `(n B) ^ |e|`, if the entries
of `β` satisfy `f (β k l) ≤ B`. -/
lemma IsSubmulAbs.le_coeff_aeval_monomial {m : ℕ} {ι : Type*} [Fintype ι] (hf : IsSubmulAbs f)
    (M : Matrix ι ι R) (e j : Fin m × ι →₀ ℕ) {B : ℝ} (hB : ∀ k l, f (M k l) ≤ B) :
    f ((aeval (blockLin fun _ ↦ M) (monomial e (1 : ℤ))).coeff j) ≤
      (Fintype.card ι * B) ^ (∑ p, e p) := by
  classical
  refine (hf.le_l1 _ j).trans ((hf.l1_aeval_blockLin_le M _).trans ?_)
  rw [support_monomial, ite_eq_right one_ne_zero, sum_singleton, coeff_monomial, ite_eq_left rfl, map_one,
    ← prod_pow_eq_pow_sum]
  refine (mul_le_of_le_one_left (prod_nonneg fun _ _ ↦ pow_nonneg
    (sum_nonneg fun _ _ ↦ hf.nonneg _) _) hf.map_one_le).trans ?_
  refine prod_le_prod₀ (fun _ _ ↦ pow_nonneg (sum_nonneg fun _ _ ↦ hf.nonneg _) _) fun p _ ↦ ?_
  refine pow_le_pow_left₀ (sum_nonneg fun _ _ ↦ hf.nonneg _) ?_ _
  calc ∑ k, f (M p.2 k) ≤ ∑ _k : ι, B := sum_le_sum fun k _ ↦ hB _ _
    _ = Fintype.card ι * B := by rw [sum_const, card_univ, nsmul_eq_mul]

end L1

/-! ### Block homogeneous monomials -/

section Monomials

variable {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exponents of the monomials which are homogeneous of degree `d h` in the block `X_h`,
written as functions `Fin m → ι → ℕ`. -/
noncomputable def blockSimplex (d : Fin m → ℕ) : Finset (Fin m → ι → ℕ) :=
  Fintype.piFinset fun h ↦ piAntidiag univ (d h)

/-- A function `Fin m → ι → ℕ` seen as an exponent of a monomial. -/
noncomputable def toExp (x : Fin m → ι → ℕ) : Fin m × ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p ↦ x p.1 p.2

omit [DecidableEq ι] in
lemma toExp_apply (x : Fin m → ι → ℕ) (p : Fin m × ι) : toExp x p = x p.1 p.2 := rfl

omit [DecidableEq ι] in
lemma toExp_injective : Function.Injective (toExp (m := m) (ι := ι)) := by
  intro x y h
  funext a b
  exact DFunLike.congr_fun h (a, b)

lemma card_blockSimplex_le (d : Fin m → ℕ) :
    #(blockSimplex (ι := ι) d) ≤ 2 ^ (Fintype.card ι * ∑ h, d h) := by
  rw [blockSimplex, Fintype.card_piFinset, mul_sum, ← prod_pow_eq_pow_sum]
  refine prod_le_prod fun h _ ↦ ?_
  calc #(piAntidiag univ (d h)) ≤ #(Fintype.piFinset fun _ : ι ↦ range (d h + 1)) := by
        refine card_le_card fun x hx ↦ ?_
        rw [mem_piAntidiag] at hx
        refine Fintype.mem_piFinset.mpr fun k ↦ mem_range.mpr (Nat.lt_succ_of_le ?_)
        rw [← hx.1]
        exact single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ k)
    _ = (d h + 1) ^ Fintype.card ι := by simp
    _ ≤ 2 ^ (Fintype.card ι * d h) := by
        rw [pow_mul']
        exact Nat.pow_le_pow_left Nat.lt_two_pow_self _

lemma blockSimplex_nonempty [Nonempty ι] (d : Fin m → ℕ) : (blockSimplex (ι := ι) d).Nonempty := by
  obtain ⟨k₀⟩ := ‹Nonempty ι›
  exact ⟨fun h ↦ Pi.single k₀ (d h), Fintype.mem_piFinset.mpr fun h ↦ mem_piAntidiag.mpr
    ⟨by simp, by simp⟩⟩

/-- The exponents of the monomials in the support of a block homogeneous polynomial lie in
`blockSimplex d`. -/
lemma IsBlockHomogeneous.exists_toExp {A : Type*} [CommSemiring A]
    {F : MvPolynomial (Fin m × ι) A} {d : Fin m → ℕ} (hF : IsBlockHomogeneous F d)
    {j : Fin m × ι →₀ ℕ} (hj : F.coeff j ≠ 0) :
    ∃ x ∈ blockSimplex (ι := ι) d, toExp x = j := by
  refine ⟨fun h k ↦ j (h, k), Fintype.mem_piFinset.mpr fun h ↦ mem_piAntidiag.mpr
    ⟨hF.sum_eq hj h, by simp⟩, Finsupp.ext fun p ↦ rfl⟩

end Monomials

/-! ### The chain rule -/

section ChainRule

variable {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma hasseDeriv_single_one {σ R : Type*} [CommSemiring R] (p : σ) (F : MvPolynomial σ R) :
    hasseDeriv (Finsupp.single p 1) F = pderiv p F := by
  induction F using MvPolynomial.induction_on' with
  | add F G hF hG => rw [hasseDeriv_add, map_add, hF, hG]
  | monomial j a =>
    rw [hasseDeriv_monomial, pderiv_monomial, Finsupp.prod_single_index (by simp),
      Nat.choose_one_right, nsmul_eq_mul, mul_comm]

lemma pderiv_blockLin (M : Matrix ι ι ℝ) (h : Fin m) (k : ι) (q : Fin m × ι) :
    pderiv (h, k) (blockLin (fun _ ↦ M) q) = if q.1 = h then C (M q.2 k) else 0 := by
  simp only [blockLin, map_sum, pderiv_C_mul, pderiv_X]
  by_cases hq : q.1 = h
  · subst hq
    rw [ite_eq_left rfl, sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · rw [ite_eq_right hq]
    refine sum_eq_zero fun b _ ↦ ?_
    simp [hq]

/-- The chain rule for the substitution `X_h = M U_h`, when `M L = 1`. -/
lemma aeval_pderiv {M L : Matrix ι ι ℝ} (hML : M * L = 1) (h : Fin m) (l : ι)
    (F : MvPolynomial (Fin m × ι) ℤ) :
    aeval (blockLin fun _ ↦ M) (pderiv (h, l) F) =
      ∑ k, C (L k l) * pderiv (h, k) (aeval (blockLin fun _ ↦ M) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG => simp only [map_add, hF, hG, mul_add, sum_add_distrib]
  | mul_X F q hF =>
    have hX : aeval (blockLin fun _ ↦ M) (pderiv (h, l) (X q : MvPolynomial (Fin m × ι) ℤ)) =
        ∑ k, C (L k l) * pderiv (h, k) (blockLin (fun _ ↦ M) q) := by
      simp only [pderiv_blockLin]
      rcases q with ⟨q1, q2⟩
      by_cases hq : q1 = h
      · subst hq
        simp only [ite_true]
        have h1 : ∑ k, C (L k l) * C (M q2 k) =
            (C ((M * L) q2 l) : MvPolynomial (Fin m × ι) ℝ) := by
          simp only [Matrix.mul_apply, map_sum, ← C_mul, mul_comm]
        rw [h1, hML]
        by_cases hl : q2 = l
        · subst hl
          simp
        · rw [Matrix.one_apply_ne hl, pderiv_X_of_ne (by simp [hl])]
          simp
      · simp only [hq, ite_false, mul_zero, sum_const_zero]
        rw [pderiv_X_of_ne (by simp [hq])]
        simp
    simp only [pderiv_mul, map_add, map_mul, aeval_X]
    rw [hF, hX, sum_mul, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ ↦ by ring

omit [DecidableEq ι] in
lemma sum_single_block (h h' : Fin m) (k : ι) :
    ∑ k', (Finsupp.single (h, k) 1 : Fin m × ι →₀ ℕ) (h', k') = if h = h' then 1 else 0 := by
  by_cases hh : h = h'
  · subst hh
    rw [ite_eq_left rfl, sum_eq_single k (fun b _ hb ↦ by simp [hb.symm])
      (by simp)]
    simp
  · rw [ite_eq_right hh]
    exact sum_eq_zero fun b _ ↦ by simp [hh]

/-- If `M L = 1`, every monomial `U ^ j` of `P_i(M U)` comes from a monomial `U ^ j'` of `P(M U)`
with `j ≤ j'`, whose degree in each block `U_h` is larger by `i_{h 1} + ⋯ + i_{h n}`. This is the
chain rule ([schmidt1980], Chapter VI, §6). -/
theorem exists_coeff_ne_zero_of_hasseDeriv {M L : Matrix ι ι ℝ} (hML : M * L = 1)
    (P : MvPolynomial (Fin m × ι) ℤ) (i j : Fin m × ι →₀ ℕ)
    (hj : (aeval (blockLin fun _ ↦ M) (hasseDeriv i P)).coeff j ≠ 0) :
    ∃ j', (aeval (blockLin fun _ ↦ M) P).coeff j' ≠ 0 ∧ j ≤ j' ∧
      ∀ h, ∑ k, j' (h, k) = ∑ k, j (h, k) + ∑ k, i (h, k) := by
  classical
  suffices H : ∀ N, ∀ i : Fin m × ι →₀ ℕ, ∑ p, i p = N → ∀ j,
      (aeval (blockLin fun _ ↦ M) (hasseDeriv i P)).coeff j ≠ 0 →
      ∃ j', (aeval (blockLin fun _ ↦ M) P).coeff j' ≠ 0 ∧ j ≤ j' ∧
        ∀ h, ∑ k, j' (h, k) = ∑ k, j (h, k) + ∑ k, i (h, k) from H _ i rfl j hj
  intro N
  induction N with
  | zero =>
    intro i hi j hj
    have hi0 : i = 0 := by
      ext p
      exact (sum_eq_zero_iff.mp hi) p (mem_univ p)
    subst hi0
    rw [hasseDeriv_zero_left] at hj
    exact ⟨j, hj, le_rfl, fun h ↦ by simp⟩
  | succ N ih =>
    intro i hi j hj
    obtain ⟨p, hp⟩ : ∃ p, i p ≠ 0 := by
      by_contra! h
      simp [h] at hi
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + Finsupp.single p 1 :=
      ⟨i - Finsupp.single p 1, (tsub_add_cancel_of_le
        (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hp))).symm⟩
    have hs1 : ∑ q, (Finsupp.single p 1 : Fin m × ι →₀ ℕ) q = 1 := by
      simp [Finsupp.single_apply]
    have hsum' : ∑ q, i' q = N := by
      simp only [Finsupp.add_apply, sum_add_distrib, hs1] at hi
      omega
    have hc := hasseDeriv_hasseDeriv i' (Finsupp.single p 1) P
    have hc0 : ((∏ v, (i' v + (Finsupp.single p 1 : Fin m × ι →₀ ℕ) v).choose (i' v) : ℕ) : ℝ)
        ≠ 0 := Nat.cast_ne_zero.mpr
      (prod_ne_zero_iff.mpr fun v _ ↦ (Nat.choose_pos (Nat.le_add_right _ _)).ne')
    rcases p with ⟨h, l⟩
    have h1 : (aeval (blockLin fun _ ↦ M) (pderiv (h, l) (hasseDeriv i' P))).coeff j ≠ 0 := by
      rw [← hasseDeriv_single_one, hc, map_mul, aeval_C, MvPolynomial.algebraMap_apply,
        coeff_C_mul]
      refine mul_ne_zero ?_ hj
      simpa using hc0
    rw [aeval_pderiv hML, coeff_sum] at h1
    obtain ⟨k, -, hk⟩ := exists_ne_zero_of_sum_ne_zero h1
    rw [coeff_C_mul, coeff_pderiv] at hk
    obtain ⟨j', hj'0, hjj', hj'sum⟩ := ih i' hsum' _ (left_ne_zero_of_mul (right_ne_zero_of_mul hk))
    refine ⟨j', hj'0, le_self_add.trans hjj', fun h' ↦ ?_⟩
    rw [hj'sum h']
    simp only [Finsupp.add_apply, sum_add_distrib, sum_single_block]
    ring

end ChainRule

/-! ### Counting monomials -/

section Counting

variable {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Chebyshev's inequality** for block homogeneous monomials ([schmidt1980], Chapter V,
Lemma 4A): the number of `x ∈ blockSimplex d` with `|∑ h, x_{h k} / d_h - m / n| > t` is at most
`m / t ^ 2` times the number of all elements of `blockSimplex d`. -/
theorem card_filter_far_mul_sq_le [Nonempty ι] (d : Fin m → ℕ) (hd : ∀ h, 0 < d h) (k : ι)
    (t : ℝ) (ht : 0 ≤ t) :
    (#((blockSimplex d).filter fun x ↦
        t < |∑ h, (x h k : ℝ) / d h - m / Fintype.card ι|) : ℝ) * t ^ 2 ≤
      m * #(blockSimplex (ι := ι) d) := by
  classical
  set n := Fintype.card ι with hn
  set T := blockSimplex (ι := ι) d with hT
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  set f : Fin m → (ι → ℕ) → ℝ := fun h y ↦ (y k : ℝ) / d h - 1 / n with hf
  have hw : ∀ x : Fin m → ι → ℕ, ∑ h, (x h k : ℝ) / d h - m / n = ∑ h, f h (x h) := by
    intro x
    show _ = ∑ h, ((x h k : ℝ) / d h - 1 / n)
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  -- the symmetry `k ↔ k'` of the simplex
  have hsymm : ∀ (D : ℕ) (k' : ι), ∑ y ∈ piAntidiag (univ : Finset ι) D, (y k : ℝ) =
      ∑ y ∈ piAntidiag (univ : Finset ι) D, (y k' : ℝ) := by
    intro D k'
    refine sum_nbij' (fun y ↦ y ∘ Equiv.swap k k') (fun y ↦ y ∘ Equiv.swap k k') ?_ ?_ ?_ ?_ ?_
    · intro y hy
      simp only [mem_piAntidiag, mem_univ, implies_true, and_true] at hy ⊢
      rw [← hy]
      exact Equiv.sum_comp _ _
    · intro y hy
      simp only [mem_piAntidiag, mem_univ, implies_true, and_true] at hy ⊢
      rw [← hy]
      exact Equiv.sum_comp _ _
    · intro y _
      funext l
      simp
    · intro y _
      funext l
      simp
    · intro y _
      simp
  have hsum : ∀ D : ℕ, (n : ℝ) * ∑ y ∈ piAntidiag (univ : Finset ι) D, (y k : ℝ) =
      #(piAntidiag (univ : Finset ι) D) * D := by
    intro D
    calc (n : ℝ) * ∑ y ∈ piAntidiag (univ : Finset ι) D, (y k : ℝ)
        = ∑ k' : ι, ∑ y ∈ piAntidiag (univ : Finset ι) D, (y k' : ℝ) := by
          rw [← sum_congr rfl fun k' _ ↦ hsymm D k', sum_const, card_univ, nsmul_eq_mul]
      _ = ∑ y ∈ piAntidiag (univ : Finset ι) D, ∑ k' : ι, (y k' : ℝ) := sum_comm
      _ = ∑ _y ∈ piAntidiag (univ : Finset ι) D, (D : ℝ) := by
          refine sum_congr rfl fun y hy ↦ ?_
          rw [← (mem_piAntidiag.mp hy).1]
          push_cast
          rfl
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hmean : ∀ h, ∑ y ∈ piAntidiag (univ : Finset ι) (d h), f h y = 0 := by
    intro h
    have h1 := hsum (d h)
    have hd0 : (0 : ℝ) < d h := by exact_mod_cast hd h
    simp only [hf]
    rw [sum_sub_distrib, ← sum_div, sum_const, nsmul_eq_mul]
    field_simp
    linarith
  have hle1 : ∀ h, ∀ y ∈ piAntidiag (univ : Finset ι) (d h), f h y * f h y ≤ 1 := by
    intro h y hy
    have hd0 : (0 : ℝ) < d h := by exact_mod_cast hd h
    have hyk : (y k : ℝ) ≤ d h := by
      rw [← (mem_piAntidiag.mp hy).1]
      exact_mod_cast single_le_sum (f := y) (fun _ _ ↦ Nat.zero_le _) (mem_univ k)
    have a0 : 0 ≤ (y k : ℝ) / d h := by positivity
    have a1 : (y k : ℝ) / d h ≤ 1 := (div_le_one hd0).mpr hyk
    have b0 : 0 ≤ 1 / (n : ℝ) := by positivity
    have b1 : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn0]
      exact_mod_cast Fintype.card_pos
    have hu : f h y ≤ 1 := by simp only [hf]; linarith
    have hl : -1 ≤ f h y := by simp only [hf]; linarith
    nlinarith [mul_nonneg (sub_nonneg.2 hu) (by linarith : (0 : ℝ) ≤ f h y + 1)]
  have hcross : ∀ h h', h ≠ h' → ∑ x ∈ T, f h (x h) * f h' (x h') = 0 := by
    intro h h' hne
    have h1 : ∑ x ∈ T, ∏ i, (if i = h then f h (x i) else if i = h' then f h' (x i) else 1) =
        ∏ i, ∑ y ∈ piAntidiag (univ : Finset ι) (d i),
          (if i = h then f h y else if i = h' then f h' y else 1) :=
      (prod_univ_sum (fun i ↦ piAntidiag (univ : Finset ι) (d i))
        fun i y ↦ if i = h then f h y else if i = h' then f h' y else 1).symm
    rw [prod_eq_zero (mem_univ h) (by simp [hmean h])] at h1
    rw [← h1]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [Fintype.prod_eq_mul h h' hne (fun i hi ↦ by simp [hi.1, hi.2])]
    simp [hne.symm]
  have hdiag : ∀ h, ∑ x ∈ T, f h (x h) * f h (x h) ≤ #T := by
    intro h
    have h1 : ∑ x ∈ T, ∏ i, (if i = h then f h (x i) * f h (x i) else 1) =
        ∏ i, ∑ y ∈ piAntidiag (univ : Finset ι) (d i), (if i = h then f h y * f h y else 1) :=
      (prod_univ_sum (fun i ↦ piAntidiag (univ : Finset ι) (d i))
        fun i y ↦ if i = h then f h y * f h y else 1).symm
    have e1 : ∑ x ∈ T, f h (x h) * f h (x h) =
        ∑ x ∈ T, ∏ i, (if i = h then f h (x i) * f h (x i) else 1) :=
      sum_congr rfl fun x _ ↦ by simp
    rw [e1, h1, hT, blockSimplex, Fintype.card_piFinset, Nat.cast_prod]
    refine prod_le_prod₀ (fun i _ ↦ ?_) fun i _ ↦ ?_
    · by_cases hi : i = h
      · subst hi
        simp only [ite_true]
        exact sum_nonneg fun _ _ ↦ mul_self_nonneg _
      · simp only [hi, ite_false]
        exact sum_nonneg fun _ _ ↦ zero_le_one
    · by_cases hi : i = h
      · subst hi
        simp only [ite_true]
        calc ∑ y ∈ piAntidiag (univ : Finset ι) (d i), f i y * f i y
            ≤ ∑ _y ∈ piAntidiag (univ : Finset ι) (d i), (1 : ℝ) :=
              sum_le_sum fun y hy ↦ hle1 i y hy
          _ = _ := by simp
      · simp [hi]
  have hvar : ∑ x ∈ T, (∑ h, f h (x h)) ^ 2 ≤ m * #T := by
    calc ∑ x ∈ T, (∑ h, f h (x h)) ^ 2 = ∑ h, ∑ h', ∑ x ∈ T, f h (x h) * f h' (x h') := by
          simp_rw [sq, sum_mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun h _ ↦ sum_comm
      _ = ∑ h, ∑ x ∈ T, f h (x h) * f h (x h) :=
          sum_congr rfl fun h _ ↦ sum_eq_single h (fun h' _ hne ↦ hcross h h' hne.symm) (by simp)
      _ ≤ ∑ _h : Fin m, (#T : ℝ) := sum_le_sum fun h _ ↦ hdiag h
      _ = m * #T := by simp
  calc (#(T.filter fun x ↦ t < |∑ h, (x h k : ℝ) / d h - m / n|) : ℝ) * t ^ 2
      = ∑ _x ∈ T.filter (fun x ↦ t < |∑ h, (x h k : ℝ) / d h - m / n|), t ^ 2 := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ T.filter (fun x ↦ t < |∑ h, (x h k : ℝ) / d h - m / n|), (∑ h, f h (x h)) ^ 2 := by
        refine sum_le_sum fun x hx ↦ ?_
        have h1 := (mem_filter.mp hx).2
        rw [hw] at h1
        calc t ^ 2 ≤ |∑ h, f h (x h)| ^ 2 := pow_le_pow_left₀ ht h1.le 2
          _ = _ := sq_abs _
    _ ≤ ∑ x ∈ T, (∑ h, f h (x h)) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ sq_nonneg _
    _ ≤ m * #T := hvar

end Counting

/-! ### Siegel's lemma over a number field -/

section Siegel

attribute [local instance] Matrix.seminormedAddCommGroup

/-- **Siegel's lemma** for a linear system with coefficients in the ring of integers of a number
field `K` and integer unknowns: if there are at least `2 r` times as many unknowns as equations,
where `r = [K : ℚ]`, there is a non-zero integer solution whose entries are bounded by the number
of unknowns times `c A`, where `A` bounds the houses of the coefficients. -/
theorem exists_int_solution_of_house_le (K : Type*) [Field K] [NumberField K] :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (α : Type u) (β : Type v) [Fintype α] [Fintype β] (a : α → β → 𝓞 K)
      (A : ℝ), (∀ r s, house (a r s : K) ≤ A) →
      2 * (Fintype.card α * Module.finrank ℚ K) ≤ Fintype.card β → 0 < Fintype.card β →
      ∃ t : β → ℤ, t ≠ 0 ∧ (∀ r, ∑ s, t s • a r s = 0) ∧
        ∀ s, |(t s : ℝ)| ≤ Fintype.card β * max 1 (c * A) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ (x : 𝓞 K) (i : K →+* ℂ),
      |(((RingOfIntegers.basis K).repr x (NumberField.equivReindex K i) : ℤ) : ℝ)| ≤
        c * house (x : K) := by
    obtain ⟨c, key⟩ : ∃ c : ℝ, ∀ (x : 𝓞 K) (i : K →+* ℂ),
        ‖(((integralBasis K).reindex (equivReindex K).symm).repr x i : ℂ)‖ ≤
          c * house (algebraMap (𝓞 K) K x) := ⟨_, house.basis_repr_norm_le_const_mul_house K⟩
    refine ⟨c, fun x i ↦ ?_⟩
    have remark := key x i
    simp only [Module.Basis.repr_reindex, Finsupp.equivMapDomain_apply, Equiv.symm_symm,
      integralBasis_repr_apply, algebraMap_int_eq, eq_intCast, Rat.cast_intCast,
      Complex.norm_intCast] at remark
    exact_mod_cast remark
  refine ⟨max c 0, le_max_right _ _, fun α β _ _ a A hA hcard hβ ↦ ?_⟩
  have hNpos : (1 : ℝ) ≤ Fintype.card β := by exact_mod_cast hβ
  by_cases hα : Fintype.card α = 0
  · have := Fintype.card_eq_zero_iff.mp hα
    obtain ⟨s₀⟩ := Fintype.card_pos_iff.mp hβ
    refine ⟨fun _ ↦ 1, fun h ↦ by simpa using congrFun h s₀, fun r ↦ isEmptyElim r, fun s ↦ ?_⟩
    simp only [Int.cast_one, abs_one]
    exact one_le_mul_of_one_le_of_one_le hNpos (le_max_left _ _)
  obtain ⟨r₀⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hα)
  obtain ⟨s₀⟩ := Fintype.card_pos_iff.mp hβ
  have hA0 : 0 ≤ A := (house_nonneg _).trans (hA r₀ s₀)
  let A' : Matrix (α × (K →+* ℂ)) β ℤ := fun rs s ↦
    (RingOfIntegers.basis K).repr (a rs.1 s) (NumberField.equivReindex K rs.2)
  have hcardα : Fintype.card (α × (K →+* ℂ)) = Fintype.card α * Module.finrank ℚ K := by
    rw [Fintype.card_prod, Embeddings.card]
  have hr : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hpos : 0 < Fintype.card (α × (K →+* ℂ)) := by
    rw [hcardα]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hα) hr
  have hlt : Fintype.card (α × (K →+* ℂ)) < Fintype.card β := by
    rw [hcardα]
    omega
  obtain ⟨t, ht0, htA, htb⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le A' hlt hpos
  refine ⟨t, ht0, fun r ↦ ?_, fun s ↦ ?_⟩
  · refine (RingOfIntegers.basis K).ext_elem fun i ↦ ?_
    obtain ⟨σ, rfl⟩ := (NumberField.equivReindex K).surjective i
    have h1 := congrFun htA (r, σ)
    simp only [mulVec, dotProduct, Pi.zero_apply, A'] at h1
    simp only [map_sum, map_zsmul, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rw [Finset.sum_apply', ← h1]
    exact sum_congr rfl fun s _ ↦ by rw [Finsupp.smul_apply, smul_eq_mul, mul_comm]
  · have hA' : ‖A'‖ ≤ max c 0 * A := by
      refine (Matrix.norm_le_iff (by positivity)).mpr fun rs s ↦ ?_
      rw [Int.norm_eq_abs]
      calc _ ≤ c * house (a rs.1 s : K) := hc _ _
        _ ≤ max c 0 * house (a rs.1 s : K) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (house_nonneg _)
        _ ≤ max c 0 * A := mul_le_mul_of_nonneg_left (hA _ _) (le_max_right _ _)
    set N := Fintype.card β with hN
    set Mr := Fintype.card (α × (K →+* ℂ)) with hMr
    have hX : 1 ≤ (N : ℝ) * max 1 ‖A'‖ := one_le_mul_of_one_le_of_one_le hNpos (le_max_left _ _)
    have he : (Mr : ℝ) / (N - Mr) ≤ 1 := by
      have h2 : (2 : ℝ) * Mr ≤ N := by
        have h4 : 2 * Mr ≤ N := by
          rw [hcardα]
          exact hcard
        exact_mod_cast h4
      have h3 : (0 : ℝ) < N - Mr := by
        have : (Mr : ℝ) < N := by exact_mod_cast hlt
        linarith
      rw [div_le_one h3]
      linarith
    have h1 : |(t s : ℝ)| ≤ ‖t‖ := by
      rw [← Int.norm_eq_abs]
      exact norm_le_pi_norm t s
    calc |(t s : ℝ)| ≤ ‖t‖ := h1
      _ ≤ ((N : ℝ) * max 1 ‖A'‖) ^ ((Mr : ℝ) / (N - Mr)) := htb
      _ ≤ ((N : ℝ) * max 1 ‖A'‖) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX he
      _ = (N : ℝ) * max 1 ‖A'‖ := Real.rpow_one _
      _ ≤ N * max 1 (max c 0 * A) := by gcongr

/-- The entries of a matrix with real algebraic entries lie in a number field, and become
algebraic integers after multiplication by a positive integer `q`. -/
theorem exists_numberField {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (hM : ∀ k l, IsAlgebraic ℚ (M k l)) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (ψ : 𝓞 K →+* ℝ) (q : ℕ)
      (β : Matrix ι ι (𝓞 K)), 0 < q ∧ ∀ k l, ψ (β k l) = q * M k l := by
  classical
  set E := IntermediateField.adjoin ℚ (Set.range fun p : ι × ι ↦ M p.1 p.2) with hE
  have hfd : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_adjoin
    (by rintro _ ⟨p, rfl⟩; exact (hM p.1 p.2).isIntegral)
  have hNF : NumberField E := ⟨⟩
  let γ : ι → ι → E := fun k l ↦
    ⟨M k l, IntermediateField.subset_adjoin _ _ ⟨(k, l), rfl⟩⟩
  have halgZ : Algebra.IsAlgebraic ℤ E :=
    ⟨fun x ↦ (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr
      ((NumberField.isAlgebraic (K := E)).isAlgebraic x)⟩
  obtain ⟨y, hy0, hy⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (univ.image fun p : ι × ι ↦ γ p.1 p.2)
  set q := y.natAbs with hq
  have hint : ∀ k l, IsIntegral ℤ ((q : ℤ) • γ k l) := by
    intro k l
    have h1 := hy (γ k l) (mem_image.mpr ⟨(k, l), mem_univ _, rfl⟩)
    rcases Int.natAbs_eq y with h | h
    · rw [← hq] at h
      rw [h] at h1
      exact h1
    · rw [← hq] at h
      rw [h, neg_smul] at h1
      simpa using h1.neg
  let β : Matrix ι ι (𝓞 E) := fun k l ↦ ⟨(q : ℤ) • γ k l, hint k l⟩
  let ψ : 𝓞 E →+* ℝ := (E.val : E →+* ℝ).comp (algebraMap (𝓞 E) E)
  refine ⟨E, inferInstance, hNF, ψ, q, β, Int.natAbs_pos.mpr hy0, fun k l ↦ ?_⟩
  simp [ψ, β, γ, zsmul_eq_mul]; rfl

/-- The entries of the inverse of a matrix with algebraic entries are algebraic. -/
theorem isAlgebraic_inv_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Matrix ι ι ℝ)
    (halg : ∀ i j, IsAlgebraic ℚ (L i j)) (k l : ι) : IsAlgebraic ℚ (L⁻¹ k l) := by
  set S := algebraicClosure ℚ ℝ with hS
  have hdet : ∀ A : Matrix ι ι ℝ, (∀ i j, A i j ∈ S) → A.det ∈ S := fun A hA ↦ by
    rw [Matrix.det_apply']
    exact sum_mem fun σ _ ↦ mul_mem (intCast_mem _ _) (prod_mem fun i _ ↦ hA _ _)
  have hL : ∀ i j, L i j ∈ S := fun i j ↦ mem_algebraicClosure_iff.mpr (halg i j)
  rw [← mem_algebraicClosure_iff, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  refine mul_mem ?_ ?_
  · rw [Ring.inverse_eq_inv']
    exact inv_mem (hdet L hL)
  · rw [Matrix.adjugate_apply]
    refine hdet _ fun i j ↦ ?_
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · exact hL _ _

end Siegel

/-! ### Coefficient bounds -/

section Bounds

variable {m : ℕ} {ι : Type*} [Fintype ι]

/-- A trivial bound for the coefficients of `P_i(M U)`, for a block homogeneous `P`. -/
theorem abs_coeff_aeval_hasseDeriv_le [Nonempty ι] (M : Matrix ι ι ℝ)
    {P : MvPolynomial (Fin m × ι) ℤ}
    {d : Fin m → ℕ} (hP : IsBlockHomogeneous P d) (i j : Fin m × ι →₀ ℕ) :
    |(aeval (blockLin fun _ ↦ M) (hasseDeriv i P)).coeff j| ≤
      (2 ^ (Fintype.card ι + 1) * (Fintype.card ι * (1 + ∑ k, ∑ l, |M k l|))) ^ (∑ h, d h) *
        height P := by
  classical
  set n := Fintype.card ι with hn
  set D := ∑ h, d h with hD
  set μ : ℝ := 1 + ∑ k, ∑ l, |M k l| with hμ
  set F := hasseDeriv i P with hF
  have hFhom := hP.hasseDeriv i
  have habs : IsSubmulAbs (fun x : ℝ ↦ |x|) :=
    ⟨abs_nonneg, abs_zero, abs_one.le, abs_add_le, fun a b ↦ (abs_mul a b).le⟩
  have hμ1 : 1 ≤ μ :=
    le_add_of_nonneg_right (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hnμ : 1 ≤ (n : ℝ) * μ := one_le_mul_of_one_le_of_one_le hn1 hμ1
  have hM : ∀ k l, |M k l| ≤ μ := fun k l ↦ by
    have h1 : |M k l| ≤ ∑ l', |M k l'| :=
      single_le_sum (f := fun l' ↦ |M k l'|) (fun _ _ ↦ abs_nonneg _) (mem_univ l)
    have h2 : ∑ l', |M k l'| ≤ ∑ k', ∑ l', |M k' l'| :=
      single_le_sum (f := fun k' ↦ ∑ l', |M k' l'|)
        (fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _) (mem_univ k)
    linarith
  have hsupp : ∀ y ∈ F.support, ∀ h, ∑ k, y (h, k) ≤ d h := fun y hy h ↦ by
    rw [hFhom.sum_eq (mem_support_iff.mp hy) h]
    exact Nat.sub_le _ _
  have hcard : (#F.support : ℝ) ≤ 2 ^ (n * D) := by
    have h1 : #F.support ≤ #(Fintype.piFinset fun p : Fin m × ι ↦ range (d p.1 + 1)) := by
      refine card_le_card_of_injOn (fun j ↦ ⇑j) (fun j hj ↦ ?_)
        (fun _ _ _ _ h ↦ DFunLike.coe_injective h)
      refine Fintype.mem_piFinset.mpr fun p ↦ mem_range.mpr (Nat.lt_succ_of_le ?_)
      exact (single_le_sum (f := fun k ↦ j (p.1, k)) (fun _ _ ↦ Nat.zero_le _)
        (mem_univ p.2)).trans (hsupp j hj p.1)
    have h2 : #(Fintype.piFinset fun p : Fin m × ι ↦ range (d p.1 + 1)) ≤ 2 ^ (n * D) := by
      rw [Fintype.card_piFinset, Fintype.prod_prod_type, hD, mul_sum, ← prod_pow_eq_pow_sum]
      refine prod_le_prod fun h _ ↦ ?_
      simp only [card_range, prod_const, card_univ]
      rw [pow_mul']
      exact Nat.pow_le_pow_left Nat.lt_two_pow_self _
    exact_mod_cast h1.trans h2
  have hterm : ∀ y ∈ F.support, |((F.coeff y : ℤ) : ℝ)| * ∏ p, (∑ k, |M p.2 k|) ^ y p ≤
      2 ^ D * height P * (n * μ) ^ D := by
    intro y hy
    have hdegy : ∑ p, y p ≤ D := by
      rw [Fintype.sum_prod_type]
      exact sum_le_sum fun h _ ↦ hsupp y hy h
    have hprod : ∏ p, (∑ k, |M p.2 k|) ^ y p ≤ ((n : ℝ) * μ) ^ D := by
      calc ∏ p, (∑ k, |M p.2 k|) ^ y p ≤ ∏ p, ((n : ℝ) * μ) ^ y p := by
            refine prod_le_prod₀ (fun _ _ ↦ by positivity) fun p _ ↦
              pow_le_pow_left₀ (by positivity) ?_ _
            calc ∑ k, |M p.2 k| ≤ ∑ _k : ι, μ := sum_le_sum fun k _ ↦ hM _ _
              _ = n * μ := by rw [sum_const, card_univ, nsmul_eq_mul]
        _ = ((n : ℝ) * μ) ^ (∑ p, y p) := prod_pow_eq_pow_sum _ _ _
        _ ≤ ((n : ℝ) * μ) ^ D := pow_le_pow_right₀ hnμ hdegy
    have hFy : F.coeff y ≠ 0 := mem_support_iff.mp hy
    have hcoeff := coeff_hasseDeriv i y P
    rw [← hF] at hcoeff
    have hPc : P.coeff (y + i) ≠ 0 := fun h0 ↦ hFy (by rw [hcoeff, h0, smul_zero])
    have hdeg : ∑ p, (y + i) p = D := by
      rw [Fintype.sum_prod_type]
      exact sum_congr rfl fun h _ ↦ hP.sum_eq hPc h
    have hch : (i.prod fun v m ↦ (y v + m).choose m) ≤ 2 ^ D := by
      rw [Finsupp.prod_fintype _ _ (by simp), ← hdeg, ← prod_pow_eq_pow_sum]
      exact prod_le_prod fun v _ ↦ (Nat.choose_le_two_pow _ _).trans (by simp)
    have hht : (P.coeff (y + i)).natAbs ≤ height P :=
      Finset.le_sup (f := fun j ↦ (P.coeff j).natAbs) (mem_support_iff.mpr hPc)
    have hPabs : |((P.coeff (y + i) : ℤ) : ℝ)| ≤ height P := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
      exact_mod_cast hht
    have hFabs : |((F.coeff y : ℤ) : ℝ)| ≤ 2 ^ D * height P := by
      rw [hcoeff, nsmul_eq_mul, Int.cast_mul, abs_mul, Int.cast_natCast,
        abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul (by exact_mod_cast hch) hPabs (abs_nonneg _) (by positivity)
    exact mul_le_mul hFabs hprod (prod_nonneg fun _ _ ↦ by positivity) (by positivity)
  calc |(aeval (blockLin fun _ ↦ M) F).coeff j|
      ≤ l1 (fun x : ℝ ↦ |x|) (aeval (blockLin fun _ ↦ M) F) := habs.le_l1 _ _
    _ ≤ ∑ y ∈ F.support, |algebraMap ℤ ℝ (F.coeff y)| * ∏ p, (∑ k, |M p.2 k|) ^ y p :=
        habs.l1_aeval_blockLin_le M F
    _ ≤ ∑ _y ∈ F.support, 2 ^ D * height P * ((n : ℝ) * μ) ^ D :=
        sum_le_sum fun y hy ↦ by simpa only [algebraMap_int_eq, eq_intCast] using hterm y hy
    _ = #F.support * (2 ^ D * height P * ((n : ℝ) * μ) ^ D) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ (n * D) * (2 ^ D * height P * ((n : ℝ) * μ) ^ D) := by gcongr
    _ = (2 ^ (n + 1) * (n * μ)) ^ D * height P := by
        simp only [mul_pow, ← pow_mul]
        ring

end Bounds

/-! ### The auxiliary polynomial -/

section Construction

variable {m : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]

lemma sum_toExp {d : Fin m → ℕ} {x : Fin m → ι → ℕ} (hx : x ∈ blockSimplex d) :
    ∑ p, toExp x p = ∑ h, d h := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun h _ ↦ ?_
  exact (mem_piAntidiag.mp (Fintype.mem_piFinset.mp hx h)).1

omit [DecidableEq ι] in
/-- A coefficient of `F(β U)` with `ψ(β) = q M`, for a monomial `F` of total degree `D`, is mapped
by `ψ` to `q ^ D` times the corresponding coefficient of `F(M U)`. -/
lemma coeff_aeval_monomial_map {R : Type*} [CommRing R] (ψ : R →+* ℝ) {q : ℕ}
    {β : Matrix ι ι R} {M : Matrix ι ι ℝ} (hβ : ∀ k l, ψ (β k l) = q * M k l)
    (e j : Fin m × ι →₀ ℕ) :
    ψ ((aeval (blockLin fun _ ↦ β) (monomial e (1 : ℤ))).coeff j) =
      (q : ℝ) ^ (∑ p, e p) * (aeval (blockLin fun _ ↦ M) (monomial e (1 : ℤ))).coeff j := by
  have hmap : ∀ p, MvPolynomial.map ψ (blockLin (fun _ : Fin m ↦ β) p) =
      C (q : ℝ) * blockLin (fun _ ↦ M) p := by
    intro p
    simp only [blockLin, map_sum, map_mul, map_C, map_X, mul_sum, hβ, ← mul_assoc]
  have hR : aeval (blockLin fun _ : Fin m ↦ M) (monomial e (1 : ℤ)) =
      ∏ p, blockLin (fun _ ↦ M) p ^ e p := by
    rw [aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (by simp)]
  rw [← coeff_map, aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (by simp), map_prod,
    hR]
  simp_rw [map_pow, hmap, mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, ← C_pow, coeff_C_mul]

omit [Fintype ι] [DecidableEq ι] in
lemma aeval_monomial_int {R : Type*} [CommRing R] (g : Fin m × ι → MvPolynomial (Fin m × ι) R)
    (e : Fin m × ι →₀ ℕ) (c : ℤ) :
    (aeval g (monomial e c)).coeff = fun j ↦ (c : R) * (aeval g (monomial e (1 : ℤ))).coeff j := by
  funext j
  rw [aeval_monomial, aeval_monomial, map_one, one_mul, MvPolynomial.algebraMap_apply,
    coeff_C_mul, algebraMap_int_eq, eq_intCast]

lemma coeff_sum_monomial_toExp {R : Type*} [CommSemiring R] (T : Finset (Fin m → ι → ℕ))
    (t : T → R) (x : T) : (∑ y : T, monomial (toExp y.1) (t y)).coeff (toExp x.1) = t x := by
  classical
  rw [coeff_sum]
  simp_rw [coeff_monomial]
  rw [sum_eq_single x (fun y _ hy ↦ ite_eq_right fun h ↦ hy (Subtype.ext (toExp_injective h)))
    (by simp), ite_eq_left rfl]

lemma height_sum_monomial_toExp_le (T : Finset (Fin m → ι → ℕ)) (t : T → ℤ) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ∀ x, |(t x : ℝ)| ≤ b) :
    (height (∑ y : T, monomial (toExp y.1) (t y)) : ℝ) ≤ b := by
  classical
  set P := ∑ y : T, monomial (toExp y.1) (t y) with hP
  have hcoeff : ∀ j, P.coeff j ≠ 0 → ∃ x : T, P.coeff j = t x := by
    intro j hj
    rw [hP, coeff_sum] at hj
    obtain ⟨x, -, hx⟩ := exists_ne_zero_of_sum_ne_zero hj
    rw [coeff_monomial] at hx
    split_ifs at hx with h
    · exact ⟨x, h ▸ coeff_sum_monomial_toExp T t x⟩
    · exact absurd rfl hx
  have h1 : height P ≤ ⌊b⌋₊ := Finset.sup_le fun j hj ↦ by
    obtain ⟨x, hx⟩ := hcoeff j (mem_support_iff.mp hj)
    rw [hx]
    refine Nat.le_floor ?_
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    exact hb x
  exact (Nat.cast_le.mpr h1).trans (Nat.floor_le hb0)

lemma isBlockHomogeneous_sum_monomial_toExp {R : Type*} [CommSemiring R] (d : Fin m → ℕ)
    (T : Finset (Fin m → ι → ℕ)) (hT : T ⊆ blockSimplex d) (t : T → R) :
    IsBlockHomogeneous (∑ y : T, monomial (toExp y.1) (t y)) d := by
  intro h
  refine IsWeightedHomogeneous.sum _ _ _ fun y _ ↦ isWeightedHomogeneous_monomial _ _ _ ?_
  rw [weight_block]
  exact (mem_piAntidiag.mp (Fintype.mem_piFinset.mp (hT y.2) h)).1

lemma isSubmulAbs_house (K : Type*) [Field K] [NumberField K] :
    IsSubmulAbs (fun a : 𝓞 K ↦ house (a : K)) where
  nonneg _ := house_nonneg _
  map_zero := by simp [house]
  map_one_le := by
    have h := house_pow (1 : K) 0
    simp only [pow_zero] at h
    simp [h]
  add_le a b := by
    push_cast
    exact house_add_le _ _
  mul_le a b := by
    push_cast
    exact house_mul_le _ _

/-- The number of "bad" block homogeneous monomials is small: at most `1 / (2 r)` times the number
of all block homogeneous monomials, if `m > 2 r n / σ ^ 2`. -/
lemma two_mul_card_bad_le [Nonempty ι] (d : Fin m → ℕ) (hd : ∀ h, 0 < d h) {σ : ℝ}
    (hσ : 0 < σ) (r : ℕ) (hm : 2 * r * Fintype.card ι / σ ^ 2 < m) :
    2 * (#((blockSimplex (ι := ι) d).filter fun x ↦
        ∃ k, m * σ < |∑ h, (x h k : ℝ) / d h - m / Fintype.card ι|) * r) ≤
      #(blockSimplex (ι := ι) d) := by
  classical
  set T := blockSimplex (ι := ι) d with hT
  set n := Fintype.card ι with hn
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hm' : 2 * r * n < m * σ ^ 2 := by rwa [div_lt_iff₀ hσ2] at hm
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
  set F : ι → Finset (Fin m → ι → ℕ) := fun k ↦
    T.filter fun x ↦ (m : ℝ) * σ < |∑ h, (x h k : ℝ) / d h - m / n| with hF
  set B := T.filter fun x ↦ ∃ k, (m : ℝ) * σ < |∑ h, (x h k : ℝ) / d h - m / n| with hB
  have hsub : B ⊆ univ.biUnion F := by
    intro x hx
    simp only [hB, mem_filter] at hx
    obtain ⟨hxT, k, hk⟩ := hx
    exact mem_biUnion.mpr ⟨k, mem_univ _, mem_filter.mpr ⟨hxT, hk⟩⟩
  have h1 : #B ≤ ∑ k, #(F k) := (card_le_card hsub).trans card_biUnion_le
  have h2 : (#B : ℝ) * (m * σ) ^ 2 ≤ n * (m * #T) := by
    calc (#B : ℝ) * (m * σ) ^ 2 ≤ (∑ k, (#(F k) : ℝ)) * (m * σ) ^ 2 := by
          gcongr
          exact_mod_cast h1
      _ = ∑ k, (#(F k) : ℝ) * (m * σ) ^ 2 := sum_mul _ _ _
      _ ≤ ∑ _k : ι, (m * #T : ℝ) :=
          sum_le_sum fun k _ ↦ card_filter_far_mul_sq_le d hd k _ (by positivity)
      _ = n * (m * #T) := by simp [hn]
  have hB0 : (0 : ℝ) ≤ #B := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have h4 : (#B : ℝ) * (m * σ ^ 2) ≤ n * #T := by
    have h3 : (#B : ℝ) * (m * σ ^ 2) * m ≤ n * #T * m := by
      calc (#B : ℝ) * ((m : ℝ) * σ ^ 2) * (m : ℝ) = (#B : ℝ) * ((m : ℝ) * σ) ^ 2 := by ring
        _ ≤ (n : ℝ) * ((m : ℝ) * (#T : ℝ)) := h2
        _ = (n : ℝ) * (#T : ℝ) * (m : ℝ) := by ring
    exact le_of_mul_le_mul_right h3 hm0
  have h5 : (#B : ℝ) * (2 * r * n) ≤ #B * (m * σ ^ 2) := mul_le_mul_of_nonneg_left hm'.le hB0
  have h6 : (2 * (#B * r) : ℝ) * n ≤ #T * n := by nlinarith
  exact_mod_cast le_of_mul_le_mul_right h6 hn0

/-- The construction of the auxiliary polynomial ([schmidt1980], Chapter VI, §7): if `m` is large,
there is a non-zero block homogeneous polynomial `P` of small height such that every monomial
`U ^ j` of `P(M U)` satisfies `|∑ h, j_{h k} / d_h - m / n| ≤ m σ` for all `k`. -/
theorem exists_aux_poly [Nonempty ι] (M : Matrix ι ι ℝ) (hM : ∀ k l, IsAlgebraic ℚ (M k l))
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C₄ : ℝ, ∀ m : ℕ, C₄ < m → ∃ C : ℝ, 1 ≤ C ∧ ∀ d : Fin m → ℕ, (∀ h, 0 < d h) →
      ∃ P : MvPolynomial (Fin m × ι) ℤ, P ≠ 0 ∧ IsBlockHomogeneous P d ∧
        (height P : ℝ) ≤ C ^ (∑ h, d h) ∧
        ∀ j, (aeval (blockLin fun _ ↦ M) P).coeff j ≠ 0 →
          ∀ k, |∑ h, (j (h, k) : ℝ) / d h - m / Fintype.card ι| ≤ m * σ := by
  obtain ⟨K, _, _, ψ, q, β, hq, hβ⟩ := exists_numberField M hM
  obtain ⟨c, hc0, hc⟩ := exists_int_solution_of_house_le.{u, u} K
  set n := Fintype.card ι with hn
  set r := Module.finrank ℚ K with hr
  refine ⟨2 * r * n / σ ^ 2, fun m hm ↦ ?_⟩
  set H : ℝ := 1 + ∑ k, ∑ l, house (β k l : K) with hH
  have hH0 : 0 ≤ ∑ k, ∑ l, house (β k l : K) :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ house_nonneg _
  have hH1 : 1 ≤ H := le_add_of_nonneg_right hH0
  have hβH : ∀ k l, house (β k l : K) ≤ H := fun k l ↦ by
    have h1 : house (β k l : K) ≤ ∑ l', house (β k l' : K) :=
      single_le_sum (f := fun l' ↦ house (β k l' : K)) (fun _ _ ↦ house_nonneg _) (mem_univ l)
    have h2 : ∑ l', house (β k l' : K) ≤ ∑ k', ∑ l', house (β k' l' : K) :=
      single_le_sum (f := fun k' ↦ ∑ l', house (β k' l' : K))
        (fun _ _ ↦ sum_nonneg fun _ _ ↦ house_nonneg _) (mem_univ k)
    linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hm0 : 0 < m := by
    have h1 : (0 : ℝ) ≤ 2 * r * n / σ ^ 2 := by positivity
    exact_mod_cast h1.trans_lt hm
  set C : ℝ := 2 ^ n * max 1 c * (n * H) with hC
  have hnH : 1 ≤ (n : ℝ) * H := one_le_mul_of_one_le_of_one_le hn1 hH1
  have hC1 : 1 ≤ C := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by norm_num)) (le_max_left _ _)) hnH
  refine ⟨C, hC1, fun d hd ↦ ?_⟩
  set T := blockSimplex (ι := ι) d with hT
  set B := T.filter fun x ↦ ∃ k, (m : ℝ) * σ < |∑ h, (x h k : ℝ) / d h - m / n| with hB
  set D := ∑ h, d h with hD
  have hD1 : 1 ≤ D := (hd ⟨0, hm0⟩).trans_le
    (single_le_sum (f := d) (fun _ _ ↦ Nat.zero_le _) (mem_univ _))
  let a : B → T → 𝓞 K := fun y x ↦
    (aeval (blockLin fun _ ↦ β) (monomial (toExp x.1) (1 : ℤ))).coeff (toExp y.1)
  have ha : ∀ y x, house (a y x : K) ≤ (n * H) ^ D := by
    intro y x
    have := (isSubmulAbs_house K).le_coeff_aeval_monomial β (toExp x.1) (toExp y.1) hβH
    rwa [sum_toExp x.2] at this
  have hcard : 2 * (Fintype.card B * r) ≤ Fintype.card T := by
    simpa only [Fintype.card_coe] using two_mul_card_bad_le d hd hσ r hm
  have hT0 : 0 < Fintype.card T := by
    simpa only [Fintype.card_coe] using (blockSimplex_nonempty d).card_pos
  obtain ⟨t, ht0, hta, htb⟩ := hc B T a _ ha hcard hT0
  set P : MvPolynomial (Fin m × ι) ℤ := ∑ x : T, monomial (toExp x.1) (t x) with hP
  have hPhom : IsBlockHomogeneous P d :=
    isBlockHomogeneous_sum_monomial_toExp d T subset_rfl t
  refine ⟨P, ?_, hPhom, ?_, ?_⟩
  · intro h0
    apply ht0
    funext x
    have := coeff_sum_monomial_toExp T t x
    rw [← hP, h0, AddMonoidAlgebra.coeff_zero] at this
    exact this.symm
  · refine height_sum_monomial_toExp_le T t (pow_nonneg (by linarith) _) fun x ↦ (htb x).trans ?_
    have h1 : (Fintype.card T : ℝ) ≤ 2 ^ (n * D) := by
      rw [Fintype.card_coe]
      exact_mod_cast card_blockSimplex_le d
    have h2 : max 1 (c * (n * H) ^ D) ≤ max 1 c * (n * H) ^ D := by
      have h3 : 1 ≤ (n * H) ^ D := one_le_pow₀ hnH
      refine max_le ?_ ?_
      · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) h3
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have h4 : max 1 c ≤ max 1 c ^ D := le_self_pow₀ (le_max_left _ _) (by omega)
    calc (Fintype.card T : ℝ) * max 1 (c * (n * H) ^ D)
        ≤ 2 ^ (n * D) * (max 1 c ^ D * (n * H) ^ D) := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_right h4 (by positivity))
      _ = C ^ D := by rw [hC]; simp only [mul_pow, pow_mul]; ring
  · intro j hj k
    have hQ := hPhom.aeval_blockLin (fun _ : Fin m ↦ M)
    obtain ⟨y, hyT, rfl⟩ := hQ.exists_toExp hj
    have hyB : y ∉ B := by
      intro hyB
      apply hj
      have h2 := congrArg ψ (hta ⟨y, hyB⟩)
      rw [map_zero, map_sum] at h2
      have h3 : (aeval (blockLin fun _ ↦ M) P).coeff (toExp y) = ∑ x : T, (t x : ℝ) *
          (aeval (blockLin fun _ ↦ M) (monomial (toExp x.1) (1 : ℤ))).coeff (toExp y) := by
        rw [hP, map_sum, coeff_sum]
        refine sum_congr rfl fun x _ ↦ ?_
        rw [aeval_monomial_int]
      have h4 : ∀ x : T, ψ (t x • a ⟨y, hyB⟩ x) = (q : ℝ) ^ D * ((t x : ℝ) *
          (aeval (blockLin fun _ ↦ M) (monomial (toExp x.1) (1 : ℤ))).coeff (toExp y)) := by
        intro x
        rw [zsmul_eq_mul, map_mul, map_intCast, coeff_aeval_monomial_map ψ hβ, sum_toExp x.2]
        ring
      simp_rw [h4, ← mul_sum, ← h3] at h2
      exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ (by exact_mod_cast hq.ne'))
    have h5 : ¬ ∃ k, (m : ℝ) * σ < |∑ h, (y h k : ℝ) / d h - m / n| :=
      fun h ↦ hyB (mem_filter.mpr ⟨hyT, h⟩)
    push Not at h5
    simpa only [toExp_apply] using h5 k

end Construction

variable {m : ℕ} {ι : Type*} [Fintype ι]

/-- **The polynomial theorem** ([evertse1993], Proposition 3.4.3). Let `L₁, …, Lₙ` be linearly
independent linear forms with real algebraic coefficients and let `σ > 0`. If `m` is large enough,
then for every tuple `d = (d₁, …, dₘ)` of positive integers there is a non-zero polynomial `P` with
integer coefficients, homogeneous of degree `d_h` in the block `X_h`, such that

* `H(P) ≤ C₅ ^ (d₁ + ⋯ + dₘ)` and `|d_{P, i}(j)| ≤ C₅ ^ (d₁ + ⋯ + dₘ)` for all `i`, `j`;
* if `(i / d) < 2 m σ`, then `d_{P, i}(j) = 0` unless
  `|∑ h, j_{h k} / d_h - m / n| ≤ 3 n m σ` for all `k`.

Here `P_i = ∑ j, d_{P, i}(j) U ^ j` is the expansion of the divided derivative `P_i` in the
variables `U_{h k} = L_k(X_h)`. -/
theorem polynomial_theorem [DecidableEq ι] [Nonempty ι] (L : Matrix ι ι ℝ) (hL : L.det ≠ 0)
    (halg : ∀ i j, IsAlgebraic ℚ (L i j)) {σ : ℝ} (hσ : 0 < σ) :
    ∃ C₄ : ℝ, ∀ m : ℕ, C₄ < m → ∃ C₅ : ℝ, 1 ≤ C₅ ∧ ∀ d : Fin m → ℕ, (∀ h, 0 < d h) →
      ∃ P : MvPolynomial (Fin m × ι) ℤ, P ≠ 0 ∧ IsBlockHomogeneous P d ∧
        (height P : ℝ) ≤ C₅ ^ (∑ h, d h) ∧
        ∀ i : Fin m × ι →₀ ℕ,
          (∀ j, |(linExpand L (hasseDeriv i P)).coeff j| ≤ C₅ ^ (∑ h, d h)) ∧
          (blockWeight d i < 2 * m * σ → ∀ j, (linExpand L (hasseDeriv i P)).coeff j ≠ 0 →
            ∀ k, |∑ h, (j (h, k) : ℝ) / d h - m / Fintype.card ι| ≤
              3 * Fintype.card ι * m * σ) := by
  obtain ⟨C₄, hC₄⟩ := exists_aux_poly L⁻¹ (isAlgebraic_inv_apply L halg) hσ
  refine ⟨C₄, fun m hm ↦ ?_⟩
  obtain ⟨C, hC1, hC⟩ := hC₄ m hm
  set n := Fintype.card ι with hn
  set μ : ℝ := 2 ^ (n + 1) * (n * (1 + ∑ k, ∑ l, |L⁻¹ k l|)) with hμ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hμ1 : 1 ≤ μ := by
    have h1 : (1 : ℝ) ≤ 1 + ∑ k, ∑ l, |L⁻¹ k l| :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    have h2 : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
    exact one_le_mul_of_one_le_of_one_le h2 (one_le_mul_of_one_le_of_one_le hn1 h1)
  refine ⟨μ * C, one_le_mul_of_one_le_of_one_le hμ1 hC1, fun d hd ↦ ?_⟩
  obtain ⟨P, hP0, hPhom, hPh, hPsupp⟩ := hC d hd
  have hσm : 0 ≤ (m : ℝ) * σ := by positivity
  refine ⟨P, hP0, hPhom, ?_, fun i ↦ ⟨fun j ↦ ?_, fun hi j hj k ↦ ?_⟩⟩
  · calc (height P : ℝ) ≤ C ^ (∑ h, d h) := hPh
      _ ≤ (μ * C) ^ (∑ h, d h) := by
          gcongr
          exact le_mul_of_one_le_left (by linarith) hμ1
  · rw [linExpand_eq_aeval]
    calc |(aeval (blockLin fun _ ↦ L⁻¹) (hasseDeriv i P)).coeff j|
        ≤ μ ^ (∑ h, d h) * height P := abs_coeff_aeval_hasseDeriv_le L⁻¹ hPhom i j
      _ ≤ μ ^ (∑ h, d h) * C ^ (∑ h, d h) := by gcongr
      _ = (μ * C) ^ (∑ h, d h) := (mul_pow _ _ _).symm
  · rw [linExpand_eq_aeval] at hj
    have hML : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L (isUnit_iff_ne_zero.mpr hL)
    obtain ⟨j', hj'0, hjj', hsum⟩ := exists_coeff_ne_zero_of_hasseDeriv hML P i j hj
    have h1 := hPsupp j' hj'0 k
    -- the difference between the weights of `j'` and `j` is at most `blockWeight d i`
    have hdiff : ∑ h, (j' (h, k) : ℝ) / d h - ∑ h, (j (h, k) : ℝ) / d h ∈
        Set.Icc 0 (blockWeight d i) := by
      rw [← Finset.sum_sub_distrib, blockWeight]
      constructor
      · refine Finset.sum_nonneg fun h _ ↦ ?_
        rw [← sub_div]
        have : (j (h, k) : ℝ) ≤ j' (h, k) := by exact_mod_cast hjj' (h, k)
        exact div_nonneg (by linarith) (Nat.cast_nonneg _)
      · refine Finset.sum_le_sum fun h _ ↦ ?_
        rw [← sub_div]
        refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
        have h2 : ∀ k', (j (h, k') : ℝ) ≤ j' (h, k') := fun k' ↦ by exact_mod_cast hjj' (h, k')
        have h3 : (∑ k', (j' (h, k') : ℝ)) = ∑ k', (j (h, k') : ℝ) + ∑ k', (i (h, k') : ℝ) := by
          exact_mod_cast hsum h
        have h4 : (j' (h, k) : ℝ) - j (h, k) ≤ ∑ k', ((j' (h, k') : ℝ) - j (h, k')) :=
          Finset.single_le_sum (f := fun k' ↦ (j' (h, k') : ℝ) - j (h, k'))
            (fun k' _ ↦ by linarith [h2 k']) (Finset.mem_univ k)
        rw [Finset.sum_sub_distrib, h3] at h4
        linarith
    obtain ⟨hd1, hd2⟩ := hdiff
    have hn' : (m : ℝ) * σ ≤ n * m * σ := by
      rw [mul_assoc]
      exact le_mul_of_one_le_left hσm hn1
    rw [abs_le] at h1 ⊢
    constructor <;> nlinarith

end Schmidt
