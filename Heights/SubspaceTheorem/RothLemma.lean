module

public import Heights.SubspaceTheorem.Wronskian

/-!
# Roth's lemma

We prove Roth's lemma ([schmidt1980], Chapter V, Theorem 10A): a non-zero polynomial
`P(X₁, …, Xₘ)` with integer coefficients, of degree at most `r_h` in `X_h`, whose degrees decrease
quickly and whose height is small, has small index at a point `(p₁ / q₁, …, pₘ / qₘ)` whose
denominators grow quickly.

The proof follows [schmidt1980], Chapter V, §§5, 6, 9, 10:

* the index of a polynomial at a rational point and its valuation properties (Lemma 6A),
  stated here with the predicate `Schmidt.IndexGE`;
* the case `m = 1`, via Gauss's lemma (`Schmidt.pow_le_height_of_dvd`);
* the induction on `m` (Theorem 10A, Lemma 10B, `Schmidt.rothStatement_succ`).

Heights of divided derivatives (Lemma 5A), generalized Wronskians (Lemma 9A) and the Wronskian
`W = V U` of the inductive step are in the file `Wronskian`.

We use one variable per block: polynomials are elements of `MvPolynomial (Fin m) ℤ`, and the
divided derivatives are the `Schmidt.hasseDeriv`.
-/

@[expose] public section

namespace Schmidt

open MvPolynomial

/-! ### The constant `ω(m, ε)` -/

/-- The constant `ω(m, ε) = 24 · 2 ^ (-m) · (ε / 12) ^ (2 ^ (m - 1))` of Roth's lemma
([schmidt1980], Chapter V, (10.2)). -/
noncomputable def rothOmega (m : ℕ) (ε : ℝ) : ℝ :=
  24 * (2 ^ m)⁻¹ * (ε / 12) ^ (2 ^ (m - 1))

lemma rothOmega_pos (m : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < rothOmega m ε := by
  unfold rothOmega
  positivity

/-- `ω(1, ε) = ε`. -/
lemma rothOmega_one (ε : ℝ) : rothOmega 1 ε = ε := by
  unfold rothOmega
  norm_num
  ring

/-- `ω(m, ε² / 12) = 2 ω(m + 1, ε)` for `m ≥ 1` ([schmidt1980], p. 145). -/
lemma rothOmega_sq (m : ℕ) [NeZero m] (ε : ℝ) :
    rothOmega m (ε ^ 2 / 12) = 2 * rothOmega (m + 1) ε := by
  unfold rothOmega
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  simp only [Nat.add_sub_cancel]
  have h1 : (ε ^ 2 / 12 / 12) ^ 2 ^ n = (ε / 12) ^ 2 ^ (n + 1) := by
    have : ε ^ 2 / 12 / 12 = (ε / 12) ^ 2 := by ring
    rw [this, ← pow_mul, ← pow_succ']
  rw [h1, pow_succ 2 (n + 1)]
  field_simp

/-- `ω(m, ε) ≤ ε² / 24` for `m ≥ 2` and `0 < ε < 1` ([schmidt1980], p. 146). -/
lemma rothOmega_le (m : ℕ) (hm : 2 ≤ m) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    rothOmega m ε ≤ ε ^ 2 / 24 := by
  unfold rothOmega
  have h0 : 0 ≤ ε / 12 := by positivity
  have h1 : ε / 12 ≤ 1 := by linarith
  have h2 : (ε / 12) ^ 2 ^ (m - 1) ≤ (ε / 12) ^ 2 :=
    pow_le_pow_of_le_one h0 h1 (by
      have : 2 ^ 1 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this)
  have h3 : ((2 : ℝ) ^ m)⁻¹ ≤ 1 / 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ^ 2 ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
    norm_num at this ⊢
    linarith
  calc 24 * ((2 : ℝ) ^ m)⁻¹ * (ε / 12) ^ 2 ^ (m - 1) ≤ 24 * (1 / 4) * (ε / 12) ^ 2 := by
        gcongr
    _ = ε ^ 2 / 24 := by ring

/-! ### The index at a rational point -/

/-- The weight `(j / r) = ∑ h, j_h / r_h` of a multi-index `j`. -/
noncomputable def rothWeight {σ : Type*} [Fintype σ] (r : σ → ℕ) (j : σ →₀ ℕ) : ℝ :=
  ∑ h, (j h : ℝ) / r h

lemma rothWeight_nonneg {σ : Type*} [Fintype σ] (r : σ → ℕ) (j : σ →₀ ℕ) :
    0 ≤ rothWeight r j :=
  Finset.sum_nonneg fun _ _ ↦ by positivity

lemma rothWeight_add {σ : Type*} [Fintype σ] (r : σ → ℕ) (a b : σ →₀ ℕ) :
    rothWeight r (a + b) = rothWeight r a + rothWeight r b := by
  simp only [rothWeight, Finsupp.add_apply, Nat.cast_add, add_div, Finset.sum_add_distrib]

lemma rothWeight_single {σ : Type*} [Fintype σ] [DecidableEq σ] (r : σ → ℕ) (v : σ) (n : ℕ) :
    rothWeight r (Finsupp.single v n) = n / r v := by
  simp only [rothWeight, Finsupp.single_apply]
  rw [Finset.sum_eq_single v (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
  simp

lemma rothWeight_mul {σ : Type*} [Fintype σ] (r : σ → ℕ) (k : ℕ) (j : σ →₀ ℕ) :
    rothWeight (fun h ↦ k * r h) j = rothWeight r j / k := by
  simp only [rothWeight, Nat.cast_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [div_div, mul_comm (r h : ℝ)]

/-- `P` has index at least `θ` at the point `α` with respect to `r`: every divided derivative
`P_j` with `(j / r) < θ` vanishes at `α` ([schmidt1980], Chapter V, §6). -/
def IndexGE {σ : Type*} [Fintype σ] (r : σ → ℕ) (α : σ → ℚ) (P : MvPolynomial σ ℚ)
    (θ : ℝ) : Prop :=
  ∀ j : σ →₀ ℕ, rothWeight r j < θ → MvPolynomial.eval α (hasseDeriv j P) = 0

section Index

variable {σ : Type*} [Fintype σ] {r : σ → ℕ} {α : σ → ℚ}

/-- Taylor's formula: `P_j(α)` is the coefficient of `X ^ j` in `P(α + X)`. -/
lemma eval_hasseDeriv_eq_coeff (P : MvPolynomial σ ℚ) (j : σ →₀ ℕ) :
    MvPolynomial.eval α (hasseDeriv j P) = (aeval (fun v ↦ C (α v) + X v) P).coeff j :=
  (coeff_aeval_C_add_X α j P).symm

lemma IndexGE.mono {P : MvPolynomial σ ℚ} {θ θ' : ℝ} (hP : IndexGE r α P θ) (h : θ' ≤ θ) :
    IndexGE r α P θ' :=
  fun j hj ↦ hP j (hj.trans_le h)

lemma indexGE_of_nonpos (P : MvPolynomial σ ℚ) {θ : ℝ} (hθ : θ ≤ 0) : IndexGE r α P θ :=
  fun j hj ↦ absurd (hj.trans_le hθ) (not_lt.mpr (rothWeight_nonneg r j))

lemma IndexGE.le {P : MvPolynomial σ ℚ} {θ : ℝ} (hP : IndexGE r α P θ) {j : σ →₀ ℕ}
    (hj : MvPolynomial.eval α (hasseDeriv j P) ≠ 0) : θ ≤ rothWeight r j := by
  by_contra h
  exact hj (hP j (not_le.mp h))

/-- [schmidt1980], Chapter V, Lemma 6A (ii). -/
lemma IndexGE.add {P Q : MvPolynomial σ ℚ} {θ : ℝ} (hP : IndexGE r α P θ)
    (hQ : IndexGE r α Q θ) : IndexGE r α (P + Q) θ := fun j hj ↦ by
  rw [hasseDeriv_add, map_add, hP j hj, hQ j hj, add_zero]

lemma IndexGE.smul {P : MvPolynomial σ ℚ} {θ : ℝ} (hP : IndexGE r α P θ) (c : ℚ) :
    IndexGE r α (c • P) θ := fun j hj ↦ by
  rw [hasseDeriv_smul, smul_eval, hP j hj, mul_zero]

lemma IndexGE.sum {ι : Type*} (s : Finset ι) {P : ι → MvPolynomial σ ℚ} {θ : ℝ}
    (hP : ∀ i ∈ s, IndexGE r α (P i) θ) : IndexGE r α (∑ i ∈ s, P i) θ := by
  induction s using Finset.cons_induction with
  | empty => exact fun j _ ↦ by simp [hasseDeriv_zero_right]
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact (hP a (Finset.mem_cons_self a s)).add (ih fun i hi ↦ hP i (Finset.mem_cons_of_mem hi))

/-- [schmidt1980], Chapter V, Lemma 6A (i). -/
lemma IndexGE.hasseDeriv {P : MvPolynomial σ ℚ} {θ : ℝ} (hP : IndexGE r α P θ)
    (i : σ →₀ ℕ) : IndexGE r α (Schmidt.hasseDeriv i P) (θ - rothWeight r i) := by
  intro j hj
  rw [hasseDeriv_hasseDeriv, map_mul, hP (i + j) (by rw [rothWeight_add]; linarith), mul_zero]

/-- [schmidt1980], Chapter V, Lemma 6A (iii), the inequality `Ind (P Q) ≥ Ind P + Ind Q`. -/
lemma IndexGE.mul {P Q : MvPolynomial σ ℚ} {θ θ' : ℝ} (hP : IndexGE r α P θ)
    (hQ : IndexGE r α Q θ') : IndexGE r α (P * Q) (θ + θ') := by
  classical
  intro j hj
  rw [eval_hasseDeriv_eq_coeff, map_mul, coeff_mul]
  refine Finset.sum_eq_zero fun x hx ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have hw : rothWeight r x.1 + rothWeight r x.2 = rothWeight r j := by
    rw [← rothWeight_add, hx]
  by_cases h1 : rothWeight r x.1 < θ
  · rw [← eval_hasseDeriv_eq_coeff, hP _ h1, zero_mul]
  · rw [← eval_hasseDeriv_eq_coeff (P := Q), hQ _ (by linarith), mul_zero]

lemma IndexGE.prod {ι : Type*} (s : Finset ι) {P : ι → MvPolynomial σ ℚ} {θ : ι → ℝ}
    (hP : ∀ i ∈ s, IndexGE r α (P i) (θ i)) :
    IndexGE r α (∏ i ∈ s, P i) (∑ i ∈ s, θ i) := by
  induction s using Finset.cons_induction with
  | empty => exact indexGE_of_nonpos _ (by simp)
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact (hP a (Finset.mem_cons_self a s)).mul
      (ih fun i hi ↦ hP i (Finset.mem_cons_of_mem hi))

/-- The index of a determinant is at least the sum over the columns of lower bounds for the
indices of the entries of the columns (consequence of [schmidt1980], Chapter V, Lemma 6A (ii),
(iii), used on p. 147). -/
lemma IndexGE.det {k : ℕ} {M : Matrix (Fin k) (Fin k) (MvPolynomial σ ℚ)} {θ : Fin k → ℝ}
    (hM : ∀ i j, IndexGE r α (M i j) (θ j)) : IndexGE r α M.det (∑ j, θ j) := by
  rw [Matrix.det_apply]
  refine IndexGE.sum _ fun τ _ ↦ ?_
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℚ]
  exact (IndexGE.prod _ fun i _ ↦ hM (τ i) i).smul _

/-- The index of a non-zero polynomial is attained: there is a divided derivative `P_j` not
vanishing at `α` such that `P` has index at least `(j / r)` at `α`. -/
lemma exists_indexGE (P : MvPolynomial σ ℚ) (hP : P ≠ 0) :
    ∃ j : σ →₀ ℕ, MvPolynomial.eval α (Schmidt.hasseDeriv j P) ≠ 0 ∧
      IndexGE r α P (rothWeight r j) := by
  classical
  have hT : (aeval (fun v ↦ C (α v) + X v) P : MvPolynomial σ ℚ) ≠ 0 := by
    intro h0
    apply hP
    have : aeval (fun v ↦ C (-α v) + X v) (aeval (fun v ↦ C (α v) + X v) P) = P := by
      rw [comp_aeval_apply]
      conv_rhs => rw [← aeval_X_left_apply P]
      refine congrArg (fun f ↦ aeval f P) (funext fun v ↦ ?_)
      simp only [map_add, aeval_C, aeval_X, algebraMap_eq, map_neg]
      ring
    rw [← this, h0, map_zero]
  obtain ⟨d, hd⟩ := ne_zero_iff.mp hT
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (aeval (fun v ↦ C (α v) + X v) P).support
    (rothWeight r) ⟨d, mem_support_iff.mpr hd⟩
  refine ⟨j, ?_, fun j' hj' ↦ ?_⟩
  · rw [eval_hasseDeriv_eq_coeff]
    exact mem_support_iff.mp hj
  · rw [eval_hasseDeriv_eq_coeff]
    by_contra h
    exact absurd (hmin j' (mem_support_iff.mpr h)) (not_le.mpr hj')

/-- [schmidt1980], Chapter V, Lemma 6A (iii), the inequality `Ind (P Q) ≤ Ind P + Ind Q`. -/
lemma exists_hasseDeriv_mul_ne_zero (hr : ∀ h, 0 < r h) {P Q : MvPolynomial σ ℚ}
    {a b : σ →₀ ℕ} (ha : MvPolynomial.eval α (Schmidt.hasseDeriv a P) ≠ 0)
    (hb : MvPolynomial.eval α (Schmidt.hasseDeriv b Q) ≠ 0) :
    ∃ c : σ →₀ ℕ, rothWeight r c ≤ rothWeight r a + rothWeight r b ∧
      MvPolynomial.eval α (Schmidt.hasseDeriv c (P * Q)) ≠ 0 := by
  classical
  set L : ℕ := ∏ h, r h with hLdef
  have hL : 0 < L := Finset.prod_pos fun h _ ↦ hr h
  set w : σ → ℕ := fun h ↦ L / r h with hwdef
  have hdvd : ∀ h, r h ∣ L := fun h ↦ Finset.dvd_prod_of_mem r (Finset.mem_univ h)
  have hw : ∀ j : σ →₀ ℕ, ((Finsupp.weight w j : ℕ) : ℝ) = L * rothWeight r j := by
    intro j
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Nat.cast_sum, rothWeight,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [smul_eq_mul, Nat.cast_mul, Nat.cast_div (hdvd h) (by exact_mod_cast (hr h).ne')]
    ring
  set f : MvPowerSeries σ ℚ :=
    ((aeval (fun v ↦ C (α v) + X v) P : MvPolynomial σ ℚ) : MvPowerSeries σ ℚ) with hf
  set g : MvPowerSeries σ ℚ :=
    ((aeval (fun v ↦ C (α v) + X v) Q : MvPolynomial σ ℚ) : MvPowerSeries σ ℚ) with hg
  have hfa : MvPowerSeries.coeff a f ≠ 0 := by
    rw [hf, coeff_coe, ← eval_hasseDeriv_eq_coeff]
    exact ha
  have hgb : MvPowerSeries.coeff b g ≠ 0 := by
    rw [hg, coeff_coe, ← eval_hasseDeriv_eq_coeff]
    exact hb
  have hfg : f * g =
      ((aeval (fun v ↦ C (α v) + X v) (P * Q) : MvPolynomial σ ℚ) : MvPowerSeries σ ℚ) := by
    rw [map_mul, coe_mul]
  have hle : (f * g).weightedOrder w ≤ ((Finsupp.weight w a + Finsupp.weight w b : ℕ) : ℕ∞) := by
    rw [MvPowerSeries.weightedOrder_mul]
    push_cast
    exact add_le_add (MvPowerSeries.weightedOrder_le w hfa) (MvPowerSeries.weightedOrder_le w hgb)
  have hfin : (((f * g).weightedOrder w).toNat : ℕ∞) = (f * g).weightedOrder w :=
    ENat.natCast_toNat (ne_top_of_le_ne_top (by simp) hle)
  obtain ⟨c, hc, hcw⟩ := MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder w hfin
  refine ⟨c, ?_, ?_⟩
  · have h1 : Finsupp.weight w c ≤ Finsupp.weight w a + Finsupp.weight w b := by
      rw [← hcw] at hle
      exact_mod_cast hle
    have h2 : ((Finsupp.weight w c : ℕ) : ℝ) ≤
        (Finsupp.weight w a : ℕ) + (Finsupp.weight w b : ℕ) := by
      exact_mod_cast h1
    rw [hw, hw, hw, ← mul_add] at h2
    exact le_of_mul_le_mul_left h2 (by exact_mod_cast hL)
  · rw [eval_hasseDeriv_eq_coeff, ← coeff_coe, ← hfg]
    exact hc

omit [Fintype σ] in
/-- The index does not change under an injective renaming of the variables. -/
lemma eval_hasseDeriv_rename {τ : Type*} {f : τ → σ} (hf : Function.Injective f)
    (j : τ →₀ ℕ) (P : MvPolynomial τ ℚ) :
    MvPolynomial.eval α (Schmidt.hasseDeriv (j.mapDomain f) (rename f P)) =
      MvPolynomial.eval (α ∘ f) (Schmidt.hasseDeriv j P) := by
  rw [hasseDeriv_rename hf, eval_rename]

lemma rothWeight_mapDomain {τ : Type*} [Fintype τ] {f : τ → σ} (_hf : Function.Injective f)
    (j : τ →₀ ℕ) : rothWeight r (j.mapDomain f) = rothWeight (r ∘ f) j := by
  classical
  have h1 : rothWeight r (j.mapDomain f) = (j.mapDomain f).sum fun h n ↦ (n : ℝ) / r h := by
    rw [rothWeight, Finsupp.sum_fintype _ _ (by simp)]
  have h2 : rothWeight (r ∘ f) j = j.sum fun h n ↦ (n : ℝ) / r (f h) := by
    rw [rothWeight, Finsupp.sum_fintype _ _ (by simp)]
    rfl
  rw [h1, h2, Finsupp.sum_mapDomain_index (by simp) (by intros; push_cast; ring)]

end Index

/-! ### Polynomials in one variable -/

section ToPoly

variable {R : Type*} [CommRing R]

/-- A polynomial in the single variable `X 0` as an element of `R[X]`. -/
noncomputable def toPoly (P : MvPolynomial (Fin 1) R) : Polynomial R :=
  aeval (fun _ ↦ Polynomial.X) P

lemma single_zero_apply_eq (e : Fin 1 →₀ ℕ) : Finsupp.single 0 (e 0) = e := by
  refine Finsupp.ext fun i ↦ ?_
  rw [Subsingleton.elim i 0, Finsupp.single_eq_same]

lemma toPoly_monomial (e : Fin 1 →₀ ℕ) (c : R) :
    toPoly (monomial e c) = Polynomial.monomial (e 0) c := by
  rw [toPoly, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_one,
    Polynomial.algebraMap_apply, Polynomial.C_mul_X_pow_eq_monomial]
  rfl

lemma coeff_toPoly (P : MvPolynomial (Fin 1) R) (n : ℕ) :
    (toPoly P).coeff n = P.coeff (Finsupp.single 0 n) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [toPoly_monomial, Polynomial.coeff_monomial, coeff_monomial, Finsupp.single_apply]
    by_cases h : e 0 = n
    · rw [ite_eq_left h, ite_eq_left (by rw [← h, single_zero_apply_eq])]
    · rw [ite_eq_right h, ite_eq_right (by rintro rfl; simp at h)]
  | add p q hp hq =>
    rw [toPoly, map_add, Polynomial.coeff_add]
    exact congrArg₂ (· + ·) hp hq

lemma toPoly_injective : Function.Injective (toPoly (R := R)) := by
  intro P Q h
  ext e
  rw [← single_zero_apply_eq e, ← coeff_toPoly, ← coeff_toPoly, h]

lemma eval_toPoly (x : R) (P : MvPolynomial (Fin 1) R) :
    (toPoly P).eval x = MvPolynomial.eval (fun _ ↦ x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [toPoly]
  | add p q hp hq => simp only [toPoly, map_add, Polynomial.eval_add] at hp hq ⊢; rw [hp, hq]
  | mul_X p v hp =>
    simp only [toPoly, map_mul, aeval_X, Polynomial.eval_mul, Polynomial.eval_X, eval_X] at hp ⊢
    rw [hp]

lemma hasseDeriv_toPoly (i : ℕ) (P : MvPolynomial (Fin 1) R) :
    Polynomial.hasseDeriv i (toPoly P) = toPoly (hasseDeriv (Finsupp.single 0 i) P) := by
  ext n
  rw [Polynomial.hasseDeriv_coeff, coeff_toPoly, coeff_toPoly, coeff_hasseDeriv,
    Finsupp.prod_single_index (by simp), Finsupp.single_add, nsmul_eq_mul]
  simp

lemma map_toPoly {S : Type*} [CommRing S] (f : R →+* S) (P : MvPolynomial (Fin 1) R) :
    (toPoly P).map f = toPoly (map f P) := by
  ext n
  rw [Polynomial.coeff_map, coeff_toPoly, coeff_toPoly, coeff_map]

end ToPoly

/-- A linear polynomial `q X - p` with coprime coefficients is primitive. -/
lemma isPrimitive_C_mul_X_sub_C {p q : ℤ} (hpq : IsCoprime p q) :
    (Polynomial.C q * Polynomial.X - Polynomial.C p).IsPrimitive := by
  intro c hc
  rw [Polynomial.C_dvd_iff_dvd_coeff] at hc
  have h1 := hc 1
  have h0 := hc 0
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one,
    Polynomial.coeff_C, Polynomial.coeff_X_zero, mul_zero, zero_sub,
    dvd_neg, one_ne_zero, ite_false, sub_zero] at h1 h0
  exact hpq.isUnit_of_dvd' h0 h1

/-- [schmidt1980], Chapter V, proof of Theorem 10A, case `m = 1`: if `f ≠ 0` has integer
coefficients and `(X - p / q) ^ l` divides `f` (`p / q` in lowest terms), then
`q ^ l ≤ |f|` (by Gauss's lemma `(q X - p) ^ l` divides `f` over `ℤ`). -/
lemma pow_le_height_of_dvd (f : MvPolynomial (Fin 1) ℤ) (hf : f ≠ 0) (p : ℤ) (q : ℕ)
    (hq : 0 < q) (hpq : IsCoprime p (q : ℤ)) (l : ℕ)
    (hdvd : (Polynomial.X - Polynomial.C ((p : ℚ) / q)) ^ l ∣
      (toPoly f).map (Int.castRingHom ℚ)) :
    q ^ l ≤ height f := by
  classical
  set g := toPoly f with hg
  have hg0 : g ≠ 0 := fun h0 ↦ hf (toPoly_injective (by rw [← hg, h0]; simp [toPoly]))
  have hprim : ((Polynomial.C (q : ℤ) * Polynomial.X - Polynomial.C p) ^ l).IsPrimitive := by
    induction l with
    | zero => simp [Polynomial.isPrimitive_one]
    | succ l ih =>
      rw [pow_succ]
      exact (ih (dvd_trans (pow_dvd_pow _ (Nat.le_succ l)) hdvd)).mul
        (isPrimitive_C_mul_X_sub_C hpq)
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hd : (Polynomial.C (q : ℤ) * Polynomial.X - Polynomial.C p) ^ l ∣ g := by
    rw [Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ hprim]
    have e : ((Polynomial.C (q : ℤ) * Polynomial.X - Polynomial.C p) ^ l).map
        (Int.castRingHom ℚ) =
        Polynomial.C ((q : ℚ) ^ l) * (Polynomial.X - Polynomial.C ((p : ℚ) / q)) ^ l := by
      rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_C, Polynomial.map_X, Polynomial.C_pow, ← mul_pow]
      congr 1
      rw [mul_sub, ← Polynomial.C_mul]
      congr 2
      simp only [eq_intCast]
      field_simp
    rw [e]
    exact ((Polynomial.isUnit_C.mpr (pow_ne_zero _ hq0).isUnit).mul_left_dvd).mpr hdvd
  obtain ⟨h, hh⟩ := hd
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hh
    exact hg0 hh
  have hlc : g.leadingCoeff = (q : ℤ) ^ l * h.leadingCoeff := by
    rw [hh, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_pow]
    congr 2
    rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.leadingCoeff_add_of_degree_lt']
    · rw [Polynomial.leadingCoeff_C_mul_X]
    · rw [Polynomial.degree_C_mul_X (by exact_mod_cast hq.ne')]
      exact (Polynomial.degree_C_le).trans_lt (by norm_num)
  have hdvd' : (q : ℤ) ^ l ∣ g.leadingCoeff := ⟨_, hlc⟩
  have hlc0 : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
  have h1 : q ^ l ≤ g.leadingCoeff.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd'
    rw [Int.natAbs_pow, Int.natAbs_natCast] at this
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hlc0) this
  have h2 : g.leadingCoeff.natAbs ≤ height f := by
    rw [Polynomial.leadingCoeff, hg, coeff_toPoly]
    have hmem : Finsupp.single 0 (toPoly f).natDegree ∈ f.support := by
      rw [mem_support_iff, ← coeff_toPoly]
      exact hlc0
    exact Finset.le_sup (f := fun j ↦ (f.coeff j).natAbs) hmem
  exact h1.trans h2

/-! ### Roth's lemma -/

/-- The statement of Roth's lemma ([schmidt1980], Chapter V, Theorem 10A) for `m` variables.
Let `0 < ε < 1 / 12`, `ω = ω(m, ε)`, let `r₁, …, rₘ` be positive integers with
`ω r_h ≥ r_{h + 1}`, let `0 < γ ≤ 1` and let `p_h / q_h` be rational numbers in lowest terms with
`q_h ^ r_h ≥ q₁ ^ (γ r₁)` and `q_h ^ (ω γ) ≥ 2 ^ (3 m)`. Let `P ≠ 0` be a polynomial with integer
coefficients, of degree at most `r_h` in `X_h`, with `|P| ≤ q₁ ^ (ω γ r₁)`. Then the index of `P`
at `(p₁ / q₁, …, pₘ / qₘ)` with respect to `r` is at most `ε`. -/
def RothStatement (m : ℕ) [NeZero m] : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 12 → ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
    (∀ h h' : Fin m, (h : ℕ) + 1 = h' → (r h' : ℝ) ≤ rothOmega m ε * r h) →
    ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ (p : Fin m → ℤ) (q : Fin m → ℕ), (∀ h, 0 < q h) →
    (∀ h, IsCoprime (p h) (q h : ℤ)) →
    (∀ h, (q 0 : ℝ) ^ (γ * r 0) ≤ (q h : ℝ) ^ (r h : ℝ)) →
    (∀ h, (2 : ℝ) ^ (3 * m) ≤ (q h : ℝ) ^ (rothOmega m ε * γ)) →
    ∀ P : MvPolynomial (Fin m) ℤ, P ≠ 0 → (∀ h, P.degreeOf h ≤ r h) →
    (height P : ℝ) ≤ (q 0 : ℝ) ^ (rothOmega m ε * γ * r 0) →
    ∃ j : Fin m →₀ ℕ, rothWeight r j ≤ ε ∧
      MvPolynomial.eval (fun h ↦ (p h : ℚ) / q h) (map (Int.castRingHom ℚ) (hasseDeriv j P)) ≠ 0

/-- Roth's lemma for one variable ([schmidt1980], Chapter V, proof of Theorem 10A, case
`m = 1`): write `P = (q X - p) ^ l R` with `R` integral by Gauss's lemma; then `q ^ l ≤ |P|`. -/
theorem rothStatement_one : RothStatement 1 := by
  intro ε hε hε1 r hr hω γ hγ hγ1 p q hq hpq h104 h105 P hP hdeg hheight
  classical
  rw [rothOmega_one] at h105 hheight
  set α : ℚ := (p 0 : ℚ) / q 0 with hα
  set g := (toPoly P).map (Int.castRingHom ℚ) with hg
  have hg0 : g ≠ 0 := by
    rw [hg, map_toPoly]
    intro h0
    apply hP
    have h1 : map (Int.castRingHom ℚ) P = 0 := toPoly_injective (by rw [h0]; simp [toPoly])
    exact map_injective (Int.castRingHom ℚ) Int.cast_injective (by rw [h1, map_zero])
  set l := g.rootMultiplicity α with hl
  have hdvd : (Polynomial.X - Polynomial.C α) ^ l ∣ g :=
    (Polynomial.le_rootMultiplicity_iff hg0).mp le_rfl
  have hne : (Polynomial.hasseDeriv l g).eval α ≠ 0 := by
    intro h0
    have : l + 1 ≤ g.rootMultiplicity α := by
      rw [Polynomial.le_rootMultiplicity_iff hg0, Polynomial.X_sub_C_pow_dvd_iff,
        ← Polynomial.taylor_apply, Polynomial.X_pow_dvd_iff]
      intro d hd
      rw [Polynomial.taylor_coeff]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | rfl
      · have h1 := hdvd
        rw [Polynomial.X_sub_C_pow_dvd_iff, ← Polynomial.taylor_apply,
          Polynomial.X_pow_dvd_iff] at h1
        have := h1 d hd
        rwa [Polynomial.taylor_coeff] at this
      · exact h0
    omega
  have hql := pow_le_height_of_dvd P hP (p 0) (q 0) (hq 0) (hpq 0) l hdvd
  -- `q > 1`
  have hq1 : (1 : ℝ) < q 0 := by
    have h1 : (1 : ℝ) ≤ q 0 := by exact_mod_cast hq 0
    rcases h1.lt_or_eq with h1 | h1
    · exact h1
    · have := h105 0
      rw [← h1, Real.one_rpow] at this
      norm_num at this
  have hl' : (l : ℝ) ≤ ε * r 0 := by
    have h2 : (q 0 : ℝ) ^ (l : ℝ) ≤ (q 0 : ℝ) ^ (ε * γ * r 0) := by
      rw [Real.rpow_natCast]
      calc (q 0 : ℝ) ^ l = ((q 0 ^ l : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ height P := by exact_mod_cast hql
        _ ≤ _ := hheight
    have h3 := (Real.rpow_le_rpow_left_iff hq1).mp h2
    have h4 : ε * γ * r 0 ≤ ε * r 0 := by
      have : (0 : ℝ) ≤ r 0 := by positivity
      nlinarith
    linarith
  refine ⟨Finsupp.single 0 l, ?_, ?_⟩
  · rw [rothWeight_single, div_le_iff₀ (by exact_mod_cast hr 0)]
    exact hl'
  · have hpt : (fun h : Fin 1 ↦ (p h : ℚ) / q h) = fun _ ↦ α := by
      funext h
      rw [Subsingleton.elim h 0]
    rw [hpt, ← eval_toPoly, ← map_toPoly, ← hasseDeriv_toPoly, ← Polynomial.hasseDeriv_map]
    exact hne

/-! ### The inductive step -/

/-- The degrees `r_h` decrease quickly: `r_{h'} ≤ ω r_h` for `h < h'`. -/
lemma roth_r_le {m : ℕ} {ω : ℝ} (_hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (r : Fin m → ℕ)
    (hω : ∀ h h' : Fin m, (h : ℕ) + 1 = h' → (r h' : ℝ) ≤ ω * r h) :
    ∀ h h' : Fin m, h < h' → (r h' : ℝ) ≤ ω * r h := by
  intro h h' hh
  obtain ⟨n, hn⟩ : ∃ n, (h' : ℕ) = h + 1 + n := ⟨h' - (h + 1), by omega⟩
  induction n generalizing h' with
  | zero => exact hω h h' (by omega)
  | succ n ihn =>
    have hlt : (h : ℕ) + 1 + n < m := by omega
    set h'' : Fin m := ⟨h + 1 + n, hlt⟩
    have h1 := ihn h'' (by simp only [h'', Fin.lt_def]; omega) rfl
    have h2 := hω h'' h' (by simp [h'']; omega)
    have h3 : (0 : ℝ) ≤ r h'' := by positivity
    nlinarith

/-- The final inequality of [schmidt1980], Chapter V, pp. 147–148 (cases I and II): if
`∑_{i < k} max(θ - i / r, 0) < k ε² / 4` with `1 ≤ k ≤ r + 1` and `0 < ε < 1`, then `θ < ε`. -/
lemma roth_final_ineq {ε θ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (k r : ℕ) (hk : 0 < k)
    (hkr : k ≤ r + 1) (hr : 0 < r)
    (h : ∑ i ∈ Finset.range k, max (θ - i / r) 0 < k * ε ^ 2 / 4) : θ < ε := by
  by_contra hθ
  push Not at hθ
  have hθ0 : 0 < θ := hε.trans_le hθ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, (θ - i / r) = n * θ - (n * (n - 1 : ℝ) / 2) / r := by
    intro n
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.sum_div]
    congr 2
    have := Finset.sum_range_id_mul_two n
    have h2 : ((∑ i ∈ Finset.range n, i : ℕ) : ℝ) * 2 = n * ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [Nat.cast_sub hn] at h2
      push_cast at h2
      linarith
  by_cases hI : (k - 1 : ℝ) / r < θ
  · -- case I
    have h1 : ∑ i ∈ Finset.range k, (θ - i / r) ≤ ∑ i ∈ Finset.range k, max (θ - i / r) 0 :=
      Finset.sum_le_sum fun i _ ↦ le_max_left _ _
    rw [hsum] at h1
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have h2 : (k : ℝ) * θ - k * (k - 1) / 2 / r < k * ε ^ 2 / 4 := by linarith
    have h3 : θ - (k - 1) / 2 / r < ε ^ 2 / 4 := by
      have : (k : ℝ) * (θ - (k - 1) / 2 / r) < k * (ε ^ 2 / 4) := by
        have e : (k : ℝ) * (θ - (k - 1) / 2 / r) = k * θ - k * (k - 1) / 2 / r := by ring
        rw [e]; linarith
      exact lt_of_mul_lt_mul_left this hk'.le
    have h4 : (k - 1 : ℝ) / 2 / r = (k - 1) / r / 2 := by ring
    rw [h4] at h3
    nlinarith
  · -- case II
    push Not at hI
    set N := ⌊θ * r⌋₊ with hN
    have hN1 : (N : ℝ) ≤ θ * r := Nat.floor_le (by positivity)
    have hN2 : θ * r < N + 1 := Nat.lt_floor_add_one _
    have hNk : N + 1 ≤ k := by
      have : (N : ℝ) ≤ k - 1 := by
        calc (N : ℝ) ≤ θ * r := hN1
          _ ≤ (k - 1) / r * r := by gcongr
          _ = k - 1 := by field_simp
      have : (N : ℝ) + 1 ≤ k := by linarith
      exact_mod_cast this
    have h1 : ∑ i ∈ Finset.range (N + 1), (θ - i / r) ≤
        ∑ i ∈ Finset.range k, max (θ - i / r) 0 := by
      calc ∑ i ∈ Finset.range (N + 1), (θ - i / r)
          ≤ ∑ i ∈ Finset.range (N + 1), max (θ - i / r) 0 :=
            Finset.sum_le_sum fun i _ ↦ le_max_left _ _
        _ ≤ ∑ i ∈ Finset.range k, max (θ - i / r) 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNk)
              fun _ _ _ ↦ le_max_right _ _
    rw [hsum] at h1
    push_cast at h1
    have h2 : θ * r * θ / 2 ≤ (N + 1) * θ - (N + 1) * N / 2 / r := by
      have e : (N + 1 : ℝ) * θ - (N + 1) * N / 2 / r = (N + 1) * (θ - N / r / 2) := by ring
      rw [e]
      have h3 : (N : ℝ) / r ≤ θ := by rw [div_le_iff₀ hr']; linarith
      have h4 : θ / 2 ≤ θ - N / r / 2 := by linarith
      calc θ * r * θ / 2 = θ * r * (θ / 2) := by ring
        _ ≤ (N + 1) * (θ - N / r / 2) := by
          apply mul_le_mul hN2.le h4 (by positivity) (by positivity)
    have hkr' : (k : ℝ) ≤ 2 * r := by
      have : (k : ℝ) ≤ r + 1 := by exact_mod_cast hkr
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      linarith
    have h5 : θ * r * θ / 2 < 2 * r * ε ^ 2 / 4 := by
      have : (k : ℝ) * ε ^ 2 / 4 ≤ 2 * r * ε ^ 2 / 4 := by gcongr
      have e : ((N : ℝ) + 1) * θ - (N + 1) * (N + 1 - 1) / 2 / r =
          (N + 1) * θ - (N + 1) * N / 2 / r := by ring
      linarith
    have h6 : θ * θ < ε * ε := by
      have : r * (θ * θ) < r * (ε * ε) := by nlinarith
      exact lt_of_mul_lt_mul_left this hr'.le
    nlinarith

/-- The inductive step of the proof of Roth's lemma ([schmidt1980], Chapter V, Theorem 10A,
"Inductive step `m - 1 ⇒ m`", pp. 142–148). -/
theorem rothStatement_succ (m : ℕ) [NeZero m] (h1 : RothStatement 1) (ih : RothStatement m) :
    RothStatement (m + 1) := by
  intro ε hε hε1 r hr hω γ hγ hγ1 p q hq hpq h104 h105 P hP hdeg hheight
  classical
  set ω := rothOmega (m + 1) ε with hωdef
  set α : Fin (m + 1) → ℚ := fun h ↦ (p h : ℚ) / q h with hα
  set F := map (Int.castRingHom ℚ) P with hF
  have hF0 : F ≠ 0 := fun h0 ↦ hP (map_injective _ Int.cast_injective (by rw [← hF, h0, map_zero]))
  have hm2 : 2 ≤ m + 1 := by have := NeZero.ne m; omega
  have hε1' : ε < 1 := by linarith
  have hω0 : 0 < ω := rothOmega_pos _ hε
  have hωε : ω ≤ ε ^ 2 / 24 := rothOmega_le (m + 1) hm2 hε hε1'
  have hω1 : ω ≤ 1 := by nlinarith
  have hq1 : ∀ h, (1 : ℝ) ≤ q h := fun h ↦ by exact_mod_cast hq h
  have hrpos : ∀ h, (0 : ℝ) < r h := fun h ↦ by exact_mod_cast hr h
  have hrdec := roth_r_le hω0.le hω1 r hω
  have hr0 : ∀ h, r h ≤ r 0 := fun h ↦ by
    by_cases h0 : h = 0
    · rw [h0]
    · have h3 := hrdec 0 h (Fin.pos_iff_ne_zero.mpr h0)
      have : (r h : ℝ) ≤ r 0 := h3.trans (by nlinarith [hrpos 0])
      exact_mod_cast this
  -- the index `θ` of `P`
  obtain ⟨j₀, hj₀, hθ⟩ := exists_indexGE (r := r) (α := α) F hF0
  refine ⟨j₀, ?_, by rwa [map_hasseDeriv]⟩
  set θ := rothWeight r j₀ with hθdef
  set rl := r (Fin.last m) with hrl
  -- the generalized Wronskian `W`
  obtain ⟨k, D, E, hk0, hkr, hDlast, hDdeg, hE, V, U, hV, hU, hW⟩ :=
    exists_wronskian m P hP rl (hdeg _)
  set W := (Matrix.of fun i j ↦ hasseDeriv (D i + Finsupp.single (Fin.last m) (E j)) P).det
    with hWdef
  obtain ⟨V', U', hV', hU', hWVU, hVH, hUH, hVdeg, hUdeg⟩ :=
    exists_int_factorization m W V U hV hU hW
  obtain ⟨hWH, hWdeg⟩ := height_det_hasseDeriv_le m P r hdeg hr0 k hkr
    (fun i j ↦ D i + Finsupp.single (Fin.last m) (E j))
  -- Lemma 10B: the index of `W` is at most `k ε² / 6`
  have h10B : ∃ c, rothWeight r c ≤ k * ε ^ 2 / 6 ∧
      MvPolynomial.eval α (hasseDeriv c (map (Int.castRingHom ℚ) W)) ≠ 0 := by
    have hq0 : (0 : ℝ) < q 0 := by linarith [hq1 0]
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    -- heights: `|W| ≤ q₁ ^ (2 ω γ r₁ k)`
    have h2q : (2 : ℝ) ^ (3 * (m + 1) * r 0) ≤ (q 0 : ℝ) ^ (ω * γ * r 0) := by
      rw [pow_mul, Real.rpow_mul hq0.le, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by positivity) (h105 0) _
    have hPq : (2 : ℝ) ^ (3 * (m + 1) * r 0) * height P ≤ (q 0 : ℝ) ^ (2 * ω * γ * r 0) := by
      calc (2 : ℝ) ^ (3 * (m + 1) * r 0) * height P
          ≤ (q 0 : ℝ) ^ (ω * γ * r 0) * (q 0 : ℝ) ^ (ω * γ * r 0) :=
            mul_le_mul h2q hheight (by positivity) (by positivity)
        _ = (q 0 : ℝ) ^ (2 * ω * γ * r 0) := by
            rw [← Real.rpow_add hq0]
            ring_nf
    have hWq : (height W : ℝ) ≤ (q 0 : ℝ) ^ (2 * ω * γ * r 0 * k) := by
      calc (height W : ℝ) ≤ (((2 ^ (3 * (m + 1) * r 0) * height P) ^ k : ℕ) : ℝ) := by
            exact_mod_cast hWH
        _ = ((2 : ℝ) ^ (3 * (m + 1) * r 0) * height P) ^ k := by push_cast; rfl
        _ ≤ ((q 0 : ℝ) ^ (2 * ω * γ * r 0)) ^ k := pow_le_pow_left₀ (by positivity) hPq k
        _ = (q 0 : ℝ) ^ (2 * ω * γ * r 0 * k) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    have hε' : 0 < ε ^ 2 / 12 := by positivity
    have hε1'' : ε ^ 2 / 12 < 1 / 12 := by nlinarith
    have hω' : rothOmega m (ε ^ 2 / 12) = 2 * ω := rothOmega_sq m ε
    -- the factor `V'` in the first `m` variables: induction hypothesis
    obtain ⟨j', hj'w, hj'ne⟩ := ih (ε ^ 2 / 12) hε' hε1'' (fun h ↦ k * r (Fin.castSucc h))
      (fun h ↦ Nat.mul_pos hk0 (hr _))
      (fun h h' hh ↦ by
        rw [hω']
        have := hω (Fin.castSucc h) (Fin.castSucc h') (by simpa using hh)
        push_cast
        nlinarith)
      γ hγ hγ1 (fun h ↦ p (Fin.castSucc h)) (fun h ↦ q (Fin.castSucc h)) (fun h ↦ hq _)
      (fun h ↦ hpq _)
      (fun h ↦ by
        have := h104 (Fin.castSucc h)
        simp only [Fin.castSucc_zero] at this ⊢
        convert pow_le_pow_left₀ (by positivity) this k using 1
        · rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
          push_cast
          ring_nf
        · rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          push_cast
          ring_nf)
      (fun h ↦ by
        rw [hω']
        calc (2 : ℝ) ^ (3 * m) ≤ 2 ^ (3 * (m + 1)) := pow_le_pow_right₀ (by norm_num) (by omega)
          _ ≤ (q (Fin.castSucc h) : ℝ) ^ (ω * γ) := h105 _
          _ ≤ (q (Fin.castSucc h) : ℝ) ^ (2 * ω * γ) :=
              Real.rpow_le_rpow_of_exponent_le (hq1 _) (by nlinarith))
      V' hV' (fun h ↦ (hVdeg h).trans (hWdeg _))
      (by
        simp only [Fin.castSucc_zero]
        rw [hω']
        calc (height V' : ℝ) ≤ height W := by exact_mod_cast hVH
          _ ≤ _ := hWq
          _ = _ := by push_cast; ring_nf)
    -- the factor `U'` in the last variable: the case `m = 1`
    obtain ⟨j'', hj''w, hj''ne⟩ := h1 (ε ^ 2 / 12) hε' hε1'' (fun _ ↦ k * rl)
      (fun _ ↦ Nat.mul_pos hk0 (hr _))
      (fun h h' hh ↦ by have := h'.2; omega)
      1 one_pos le_rfl (fun _ ↦ p (Fin.last m)) (fun _ ↦ q (Fin.last m)) (fun _ ↦ hq _)
      (fun _ ↦ hpq _) (fun _ ↦ by simp)
      (fun _ ↦ by
        simp only [rothOmega_one, mul_one]
        calc (2 : ℝ) ^ (3 * 1) ≤ 2 ^ (3 * (m + 1)) := pow_le_pow_right₀ (by norm_num) (by omega)
          _ ≤ (q (Fin.last m) : ℝ) ^ (ω * γ) := h105 _
          _ ≤ (q (Fin.last m) : ℝ) ^ (ε ^ 2 / 12) :=
              Real.rpow_le_rpow_of_exponent_le (hq1 _) (by nlinarith))
      U' hU' (fun h ↦ by
        have : h = 0 := Subsingleton.elim _ _
        subst this
        exact hUdeg.trans (hWdeg _))
      (by
        simp only [rothOmega_one, mul_one]
        have hql : (0 : ℝ) < q (Fin.last m) := by linarith [hq1 (Fin.last m)]
        calc (height U' : ℝ) ≤ height W := by exact_mod_cast hUH
          _ ≤ (q 0 : ℝ) ^ (2 * ω * γ * r 0 * k) := hWq
          _ = ((q 0 : ℝ) ^ (γ * r 0)) ^ (2 * ω * k) := by
              rw [← Real.rpow_mul hq0.le]
              ring_nf
          _ ≤ ((q (Fin.last m) : ℝ) ^ (rl : ℝ)) ^ (2 * ω * k) :=
              Real.rpow_le_rpow (by positivity) (h104 _) (by positivity)
          _ = (q (Fin.last m) : ℝ) ^ (2 * ω * (k * rl)) := by
              rw [← Real.rpow_mul hql.le]
              ring_nf
          _ ≤ (q (Fin.last m) : ℝ) ^ (ε ^ 2 / 12 * ((k * rl : ℕ) : ℝ)) := by
              refine Real.rpow_le_rpow_of_exponent_le (hq1 _) ?_
              push_cast
              have : (0 : ℝ) ≤ k * rl := by positivity
              nlinarith)
    -- the product
    have hWmap : map (Int.castRingHom ℚ) W = rename Fin.castSucc (map (Int.castRingHom ℚ) V') *
        rename (fun _ : Fin 1 ↦ Fin.last m) (map (Int.castRingHom ℚ) U') := by
      rw [hWVU, map_mul, map_rename, map_rename]
    have hinj1 : Function.Injective (fun _ : Fin 1 ↦ Fin.last m) := fun a b _ ↦
      Subsingleton.elim a b
    have hV1 : MvPolynomial.eval α (hasseDeriv (j'.mapDomain Fin.castSucc)
        (rename Fin.castSucc (map (Int.castRingHom ℚ) V'))) ≠ 0 := by
      rw [eval_hasseDeriv_rename (Fin.castSucc_injective m), ← map_hasseDeriv]
      exact hj'ne
    have hU1 : MvPolynomial.eval α (hasseDeriv (j''.mapDomain fun _ ↦ Fin.last m)
        (rename (fun _ : Fin 1 ↦ Fin.last m) (map (Int.castRingHom ℚ) U'))) ≠ 0 := by
      rw [eval_hasseDeriv_rename hinj1, ← map_hasseDeriv]
      exact hj''ne
    obtain ⟨c, hc, hcne⟩ := exists_hasseDeriv_mul_ne_zero hr hV1 hU1
    refine ⟨c, hc.trans ?_, by rwa [hWmap]⟩
    rw [rothWeight_mapDomain (Fin.castSucc_injective m), rothWeight_mapDomain hinj1]
    have e1 : rothWeight (r ∘ Fin.castSucc) j' =
        k * rothWeight (fun h ↦ k * r (Fin.castSucc h)) j' := by
      rw [rothWeight_mul]
      field_simp
      rfl
    have e2 : rothWeight (r ∘ fun _ : Fin 1 ↦ Fin.last m) j'' =
        k * rothWeight (fun _ ↦ k * rl) j'' := by
      rw [rothWeight_mul (fun _ ↦ rl)]
      field_simp
      rfl
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left (add_le_add hj'w hj''w) hk'.le
    linarith
  -- the lower bound for the index of `W`
  have hwt : ∀ i j : Fin k, rothWeight r (D i + Finsupp.single (Fin.last m) (E j)) ≤
      ε ^ 2 / 24 + j / rl := by
    intro i j
    have hrl : (0 : ℝ) < rl := hrpos _
    rw [rothWeight_add, rothWeight_single]
    have h3 : rothWeight r (D i) ≤ ω := by
      calc rothWeight r (D i) ≤ ∑ h, (D i h : ℝ) * (ω / rl) := by
            refine Finset.sum_le_sum fun h _ ↦ ?_
            by_cases hh : h = Fin.last m
            · rw [hh, hDlast]
              simp
            · have h4 := hrdec h (Fin.last m) (Fin.lt_last_iff_ne_last.mpr hh)
              rw [div_eq_mul_inv]
              refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
              rw [inv_eq_one_div, div_le_div_iff₀ (hrpos h) hrl]
              linarith
        _ = ω / rl * (D i).degree := by
            rw [Finsupp.degree_eq_sum, ← Finset.sum_mul, mul_comm]
            push_cast
            rfl
        _ ≤ ω / rl * rl := by
            gcongr
            have := hDdeg i
            have : (i : ℕ) < k := i.2
            omega
        _ = ω := by field_simp
    have h5 : (E j : ℝ) / rl ≤ j / rl := by
      gcongr
      exact_mod_cast hE j
    linarith
  have hlow : IndexGE r α (map (Int.castRingHom ℚ) W)
      (∑ j : Fin k, max (θ - ε ^ 2 / 24 - j / rl) 0) := by
    rw [hWdef, RingHom.map_det]
    refine IndexGE.det fun i j ↦ ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_hasseDeriv, ← hF]
    rcases le_total (θ - ε ^ 2 / 24 - j / rl) 0 with h0 | h0
    · rw [max_eq_right h0]
      exact indexGE_of_nonpos _ le_rfl
    · rw [max_eq_left h0]
      exact (hθ.hasseDeriv _).mono (by linarith [hwt i j])
  obtain ⟨c, hc, hcne⟩ := h10B
  have h2 := hlow.le hcne
  apply le_of_lt
  refine roth_final_ineq hε hε1' k rl hk0 hkr (hr _) ?_
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  calc ∑ i ∈ Finset.range k, max (θ - i / rl) 0
      ≤ ∑ j : Fin k, (max (θ - ε ^ 2 / 24 - j / rl) 0 + ε ^ 2 / 24) := by
        rw [Finset.sum_range]
        refine Finset.sum_le_sum fun j _ ↦ ?_
        refine max_le ?_ (by positivity)
        have := le_max_left (θ - ε ^ 2 / 24 - j / rl) 0
        linarith
    _ = ∑ j : Fin k, max (θ - ε ^ 2 / 24 - j / rl) 0 + k * (ε ^ 2 / 24) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ < k * ε ^ 2 / 4 := by nlinarith [sq_nonneg ε, mul_pos hk' (pow_pos hε 2)]

/-- **Roth's lemma** ([schmidt1980], Chapter V, Theorem 10A). -/
theorem roth_lemma (m : ℕ) [NeZero m] : RothStatement m := by
  have key : ∀ n : ℕ, RothStatement (n + 1) := by
    intro n
    induction n with
    | zero => exact rothStatement_one
    | succ n ih => exact rothStatement_succ (n + 1) rothStatement_one ih
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  exact key n

end Schmidt
