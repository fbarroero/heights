module

public import Heights.SubspaceTheorem.RothLemma

/-!
# Schmidt's generalisation of Roth's lemma

We prove `Schmidt.generalized_roth_lemma` ([evertse1993], Proposition 3.4.2, [schmidt1980],
Chapter VI, Theorem 10B), following [schmidt1980], Chapter VI, §10: a polynomial `P` in `m` blocks
of `n` variables has small index on a product `V₁ × ⋯ × Vₘ` of rational hyperplanes. It is
deduced from Roth's lemma `Schmidt.roth_lemma` ([schmidt1980], Chapter V, Theorem 10A) as follows.

* For every `h` we choose a coordinate `k₁ h` with `|c_{h, k₁}| = ‖c_h‖` and, by
  [schmidt1980], Chapter VI, Lemma 10A (`Schmidt.exists_gcd_le_rpow`), a second coordinate `k₂ h`
  with `gcd(c_{h, k₁}, c_{h, k₂}) ≤ |c_{h, k₁}| ^ ((n - 2) / (n - 1))`.
* From `P` we construct a polynomial `Q(X₁, …, Xₘ)` in one variable per block, with
  `|Q| ≤ |P|`, such that a divided derivative `Q_j` not vanishing at the point
  `α_h = -c_{h, k₂} / c_{h, k₁}` gives a divided derivative `P_i` of the same weight not vanishing
  at a rational point of `V₁ × ⋯ × Vₘ` (`Schmidt.exists_reduction`; this is the construction of
  `P̃` in [schmidt1980], pp. 192–194, together with [schmidt1980], Chapter VI, Lemma 4C).
* Roth's lemma applies to `Q` at `α`, with `γ / (n - 1)` in place of `γ`.
-/

@[expose] public section

namespace Schmidt

open MvPolynomial

/-! ### Setting some variables to zero -/

section ZeroOn

variable {σ R : Type*} [CommSemiring R]

/-- Put the variables `X v` with `S v` equal to `0`. -/
noncomputable def zeroOn (S : σ → Prop) [DecidablePred S] :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun v ↦ if S v then 0 else X v

variable (S : σ → Prop) [DecidablePred S]

lemma zeroOn_monomial (a : σ →₀ ℕ) (c : R) :
    zeroOn S (monomial a c) = if ∀ v ∈ a.support, ¬ S v then monomial a c else 0 := by
  classical
  rw [zeroOn, aeval_monomial, algebraMap_eq, Finsupp.prod]
  split_ifs with h
  · rw [monomial_eq, Finsupp.prod]
    congr 1
    refine Finset.prod_congr rfl fun v hv ↦ ?_
    simp [h v hv]
  · push Not at h
    obtain ⟨v, hv, hS⟩ := h
    rw [Finset.prod_eq_zero hv (by simp [hS, zero_pow (Finsupp.mem_support_iff.mp hv)]),
      mul_zero]

lemma coeff_zeroOn (a : σ →₀ ℕ) (H : MvPolynomial σ R) :
    (zeroOn S H).coeff a = if ∀ v ∈ a.support, ¬ S v then H.coeff a else 0 := by
  classical
  induction H using MvPolynomial.induction_on' with
  | monomial b c =>
    rw [zeroOn_monomial, coeff_monomial]
    by_cases hab : b = a
    · subst hab
      split_ifs <;> simp_all
    · split_ifs <;> simp [coeff_monomial, hab]
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    split_ifs <;> simp

lemma eval_zeroOn {A : Type*} [CommSemiring A] [Algebra R A] (y : σ → A)
    (H : MvPolynomial σ R) :
    aeval y (zeroOn S H) = aeval (fun v ↦ if S v then 0 else y v) H := by
  rw [zeroOn, comp_aeval_apply]
  congr 2
  funext v
  split_ifs <;> simp

lemma hasseDeriv_zeroOn {i : σ →₀ ℕ} (hi : ∀ v ∈ i.support, ¬ S v) (H : MvPolynomial σ R) :
    hasseDeriv i (zeroOn S H) = zeroOn S (hasseDeriv i H) := by
  classical
  ext k
  rw [coeff_hasseDeriv, coeff_zeroOn, coeff_zeroOn, coeff_hasseDeriv]
  have hiff : (∀ v ∈ (k + i).support, ¬ S v) ↔ ∀ v ∈ k.support, ¬ S v := by
    constructor
    · intro h v hv
      exact h v (Finsupp.mem_support_iff.mpr (by
        have := Finsupp.mem_support_iff.mp hv
        simp only [Finsupp.add_apply]
        omega))
    · intro h v hv
      by_cases hk : v ∈ k.support
      · exact h v hk
      · have hk0 : k v = 0 := Finsupp.notMem_support_iff.mp hk
        have : i v ≠ 0 := by
          have := Finsupp.mem_support_iff.mp hv
          simp only [Finsupp.add_apply] at this
          omega
        exact hi v (Finsupp.mem_support_iff.mpr this)
  by_cases hk : ∀ v ∈ k.support, ¬ S v
  · rw [ite_eq_left (hiff.mpr hk), ite_eq_left hk]
  · rw [ite_eq_right (mt hiff.mp hk), ite_eq_right hk, smul_zero]

/-- The coefficient of `X ^ a` in `H_κ`, when `a` and `κ` have disjoint supports. -/
lemma coeff_hasseDeriv_of_disjoint {κ a : σ →₀ ℕ} (h : ∀ v ∈ κ.support, a v = 0)
    (H : MvPolynomial σ R) : (hasseDeriv κ H).coeff a = H.coeff (a + κ) := by
  rw [coeff_hasseDeriv, Finsupp.prod, Finset.prod_eq_one (fun v hv ↦ by rw [h v hv, zero_add,
    Nat.choose_self]), one_smul]

lemma coeff_zeroOn_hasseDeriv_filter (e : σ →₀ ℕ) (H : MvPolynomial σ R) :
    (zeroOn S (hasseDeriv (e.filter S) H)).coeff (e.filter (fun v ↦ ¬ S v)) = H.coeff e := by
  have h1 : ∀ v ∈ (e.filter (fun v ↦ ¬ S v)).support, ¬ S v := fun v hv ↦ by
    rw [Finsupp.support_filter, Finset.mem_filter] at hv
    exact hv.2
  rw [coeff_zeroOn, ite_eq_left h1]
  rw [coeff_hasseDeriv_of_disjoint (fun v hv ↦ by
    rw [Finsupp.support_filter, Finset.mem_filter] at hv
    simp [hv.2]), add_comm, Finsupp.filter_add_filter_not]

lemma aeval_C_mul_X_monomial (s : σ → R) (j : σ →₀ ℕ) (a : R) :
    aeval (fun v ↦ C (s v) * X v) (monomial j a) =
      monomial j (a * j.prod fun v k ↦ s v ^ k) := by
  rw [aeval_monomial, algebraMap_eq, Finsupp.prod, monomial_eq, Finsupp.prod, Finsupp.prod,
    C_mul, map_prod, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [mul_pow, map_pow]

/-- Rescaling the variables: the coefficient of `X ^ t` in `H(s₁ X₁, …)` is `s ^ t` times the
coefficient of `X ^ t` in `H`. -/
lemma coeff_aeval_C_mul_X (s : σ → R) (t : σ →₀ ℕ) (H : MvPolynomial σ R) :
    (aeval (fun v ↦ C (s v) * X v) H).coeff t = (t.prod fun v k ↦ s v ^ k) * H.coeff t := by
  classical
  induction H using MvPolynomial.induction_on' with
  | monomial j a =>
    rw [aeval_C_mul_X_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]

/-- A linear substitution which is the identity on the variables `X v` with `S v` and sends the
other variables to linear forms (or `0`) does not change the coefficient of `X ^ κ` in `T`, provided
that the monomials of `T` involving a variable outside `S` have degree different from that of
`κ`. -/
lemma coeff_aeval_of_isHomogeneous (L : σ → MvPolynomial σ R) (hLS : ∀ v, S v → L v = X v)
    (hL : ∀ v, (L v).IsHomogeneous 1) (T : MvPolynomial σ R) (κ : σ →₀ ℕ)
    (hT : ∀ e ∈ T.support, (∃ v ∈ e.support, ¬ S v) → e.degree ≠ κ.degree) :
    (aeval L T).coeff κ = T.coeff κ := by
  classical
  conv_lhs => rw [T.as_sum]
  rw [map_sum]
  simp only [aeval_monomial, algebraMap_eq]
  rw [coeff_sum]
  simp only [coeff_C_mul]
  have hX : ∀ e : σ →₀ ℕ, (∀ v ∈ e.support, S v) → (e.prod fun i k ↦ L i ^ k) = monomial e 1 := by
    intro e he
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, Finsupp.prod]
    exact Finset.prod_congr rfl fun v hv ↦ by rw [hLS v (he v hv)]
  have hhom : ∀ e : σ →₀ ℕ, (e.prod fun i k ↦ L i ^ k).IsHomogeneous e.degree := by
    intro e
    rw [Finsupp.prod, Finsupp.degree]
    have := IsHomogeneous.prod e.support (fun i ↦ L i ^ e i) (fun i ↦ 1 * e i)
      (fun i _ ↦ (hL i).pow (e i))
    simp only [one_mul] at this
    exact this
  rw [Finset.sum_eq_single κ]
  · by_cases hκ : ∀ v ∈ κ.support, S v
    · rw [hX κ hκ, coeff_monomial, ite_eq_left rfl, mul_one]
    · by_cases hT0 : T.coeff κ = 0
      · rw [hT0, zero_mul]
      · push Not at hκ
        exact absurd rfl (hT κ (mem_support_iff.mpr hT0) hκ)
  · intro e he hne
    by_cases heS : ∀ v ∈ e.support, S v
    · rw [hX e heS, coeff_monomial, ite_eq_right hne, mul_zero]
    · push Not at heS
      rw [(hhom e).coeff_eq_zero (Ne.symm (hT e he heS)), mul_zero]
  · intro h
    rw [notMem_support_iff.mp h, zero_mul]

end ZeroOn

section Blocks

variable {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (c : Fin m → ι → ℚ) (k₁ : Fin m → ι)

/-- The substitution `X_{h, k₁} ↦ c_h ⬝ X_h` (the other variables are fixed). -/
noncomputable def substL (v : Fin m × ι) : MvPolynomial (Fin m × ι) ℚ :=
  if v.2 = k₁ v.1 then ∑ k, C (c v.1 k) * X (v.1, k) else X v

/-- The inverse substitution `X_{h, k₁} ↦ (X_{h, k₁} - ∑_{k ≠ k₁} c_{h k} X_{h k}) / c_{h, k₁}`. -/
noncomputable def substLInv (v : Fin m × ι) : MvPolynomial (Fin m × ι) ℚ :=
  if v.2 = k₁ v.1 then
    C (c v.1 (k₁ v.1))⁻¹ * (X v - ∑ k ∈ Finset.univ.erase (k₁ v.1), C (c v.1 k) * X (v.1, k))
  else X v

lemma aeval_substL_substLInv (hc : ∀ h, c h (k₁ h) ≠ 0) (F : MvPolynomial (Fin m × ι) ℚ) :
    aeval (substL c k₁) (aeval (substLInv c k₁) F) = F := by
  rw [comp_aeval_apply]
  conv_rhs => rw [← aeval_X_left_apply F]
  congr 2
  funext v
  by_cases hv : v.2 = k₁ v.1
  · have h1 : ∀ k ∈ Finset.univ.erase (k₁ v.1), substL c k₁ (v.1, k) = X (v.1, k) := fun k hk ↦ by
      rw [substL, ite_eq_right (Finset.ne_of_mem_erase hk)]
    have h2 : substL c k₁ v = ∑ k, C (c v.1 k) * X (v.1, k) := by rw [substL, ite_eq_left hv]
    have hv' : v = (v.1, k₁ v.1) := Prod.ext rfl hv
    rw [substLInv, ite_eq_left hv]
    simp only [map_mul, map_sub, map_sum, aeval_C, aeval_X, algebraMap_eq]
    have h3 : ∑ k ∈ Finset.univ.erase (k₁ v.1), C (c v.1 k) * substL c k₁ (v.1, k) =
        ∑ k ∈ Finset.univ.erase (k₁ v.1), C (c v.1 k) * X (v.1, k) :=
      Finset.sum_congr rfl fun k hk ↦ by rw [h1 k hk]
    rw [h2, h3, ← Finset.add_sum_erase _ _ (Finset.mem_univ (k₁ v.1)), add_sub_cancel_right,
      ← mul_assoc,
      ← C_mul, inv_mul_cancel₀ (hc v.1), C_1, one_mul, ← hv']
  · simp [substLInv, substL, hv]

/-- [schmidt1980], Chapter VI, Lemma 4C (with derivatives in the directions `X_{h, k₁}` only): if
the monomial `X ^ E` occurs in `F` written in the coordinates `(c_h ⬝ X_h, X_{h k})_{k ≠ k₁}`,
then the divided derivative of `F` whose order is the part of `E` in the variables `X_{h, k₁}`
does not vanish at some rational point of `V₁ × ⋯ × Vₘ`, `V_h : c_h ⬝ X_h = 0`. -/
lemma exists_point_of_coeff_ne_zero (hc : ∀ h, c h (k₁ h) ≠ 0) (F : MvPolynomial (Fin m × ι) ℚ)
    (E : Fin m × ι →₀ ℕ) (hE : (aeval (substLInv c k₁) F).coeff E ≠ 0) :
    ∃ z : Fin m × ι → ℚ, (∀ h, ∑ k, c h k * z (h, k) = 0) ∧
      MvPolynomial.eval z (hasseDeriv (E.filter fun v ↦ v.2 = k₁ v.1) F) ≠ 0 := by
  classical
  set K1 : Fin m × ι → Prop := fun v ↦ v.2 = k₁ v.1 with hK1
  set G := aeval (substLInv c k₁) F with hG
  set t := E.filter K1 with ht
  have hR : zeroOn K1 (hasseDeriv t G) ≠ 0 := by
    intro h0
    have := coeff_zeroOn_hasseDeriv_filter K1 E G
    rw [h0] at this
    exact hE (by simpa using this.symm)
  obtain ⟨y, hy⟩ : ∃ y, MvPolynomial.eval y (zeroOn K1 (hasseDeriv t G)) ≠ 0 := by
    by_contra! h
    exact hR (MvPolynomial.funext fun x ↦ by rw [h x, map_zero])
  set y' : Fin m × ι → ℚ := fun v ↦ if K1 v then 0 else y v with hy'
  replace hy : MvPolynomial.eval y' (hasseDeriv t G) ≠ 0 := by
    rwa [show MvPolynomial.eval y (zeroOn K1 (hasseDeriv t G)) =
      MvPolynomial.eval y' (hasseDeriv t G) from eval_zeroOn K1 y _] at hy
  set z : Fin m × ι → ℚ := fun v ↦ MvPolynomial.eval y' (substLInv c k₁ v) with hz
  set s : Fin m × ι → ℚ := fun v ↦ if K1 v then (c v.1 (k₁ v.1))⁻¹ else 0 with hs
  have key : ∀ v, zeroOn (fun u ↦ ¬ K1 u) (aeval (fun u ↦ C (y' u) + X u) (substLInv c k₁ v)) =
      C (z v) + C (s v) * X v := by
    intro v
    by_cases hv : K1 v
    · have hv' : v.2 = k₁ v.1 := hv
      have hzv : z v = (c v.1 (k₁ v.1))⁻¹ *
          (y' v - ∑ k ∈ Finset.univ.erase (k₁ v.1), c v.1 k * y' (v.1, k)) := by
        simp [hz, substLInv, hv']
      have hsv : s v = (c v.1 (k₁ v.1))⁻¹ := by simp [hs, hv]
      rw [hzv, hsv, substLInv, ite_eq_left hv']
      simp only [zeroOn, map_mul, map_sub, map_sum, map_add, aeval_C, aeval_X, algebraMap_eq]
      rw [Finset.sum_congr rfl (fun k hk ↦ by
        rw [ite_eq_left (show ¬ K1 (v.1, k) from Finset.ne_of_mem_erase hk)]),
        ite_eq_right (not_not.mpr hv)]
      simp only [add_zero]
      ring
    · have hv' : ¬ v.2 = k₁ v.1 := hv
      have hzv : z v = y' v := by simp [hz, substLInv, hv']
      have hsv : s v = 0 := by simp [hs, hv]
      rw [hzv, hsv, substLInv, ite_eq_right hv']
      simp [zeroOn, hv]
  have h2 : MvPolynomial.eval y' (hasseDeriv t G) =
      (t.prod fun v k ↦ s v ^ k) * MvPolynomial.eval z (hasseDeriv t F) := by
    have ht' : ∀ v ∈ t.support, ¬ ¬ K1 v := fun v hv ↦ by
      rw [ht, Finsupp.support_filter, Finset.mem_filter] at hv
      exact not_not.mpr hv.2
    have h3 : (aeval (fun v ↦ C (y' v) + X v) G).coeff t =
        (zeroOn (fun u ↦ ¬ K1 u) (aeval (fun v ↦ C (y' v) + X v) G)).coeff t := by
      rw [coeff_zeroOn, ite_eq_left ht']
    have h4 : zeroOn (fun u ↦ ¬ K1 u) (aeval (fun v ↦ C (y' v) + X v) G) =
        aeval (fun v ↦ C (s v) * X v) (aeval (fun v ↦ C (z v) + X v) F) := by
      rw [hG, comp_aeval_apply (φ := aeval fun v ↦ C (y' v) + X v),
        comp_aeval_apply (φ := zeroOn fun u ↦ ¬ K1 u), comp_aeval_apply]
      refine congrArg (fun f ↦ aeval f F) (funext fun v ↦ ?_)
      simp only [map_add, aeval_C, aeval_X, algebraMap_eq]
      exact key v
    rw [← coeff_aeval_C_add_X, ← coeff_aeval_C_add_X, h3, h4, coeff_aeval_C_mul_X]
  refine ⟨z, fun h ↦ ?_, ?_⟩
  · have hz1 : z (h, k₁ h) = (c h (k₁ h))⁻¹ *
        (y' (h, k₁ h) - ∑ k ∈ Finset.univ.erase (k₁ h), c h k * y' (h, k)) := by
      simp [hz, substLInv]
    have hz2 : ∀ k ∈ Finset.univ.erase (k₁ h), z (h, k) = y' (h, k) := fun k hk ↦ by
      simp [hz, substLInv, Finset.ne_of_mem_erase hk]
    have hy0 : y' (h, k₁ h) = 0 := by simp [hy', hK1]
    have hz3 : ∑ k ∈ Finset.univ.erase (k₁ h), c h k * z (h, k) =
        ∑ k ∈ Finset.univ.erase (k₁ h), c h k * y' (h, k) :=
      Finset.sum_congr rfl fun k hk ↦ by rw [hz2 k hk]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (k₁ h)), hz3, hz1, hy0, ← mul_assoc,
      mul_inv_cancel₀ (hc h)]
    ring
  · rw [h2] at hy
    exact right_ne_zero_of_mul hy

end Blocks


section Blocks2

variable {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (c : Fin m → ι → ℚ) (k₁ k₂ : Fin m → ι)

/-- The variables `X_{h k}` with `k ∉ {k₁ h, k₂ h}`. -/
def IsRest (v : Fin m × ι) : Prop := v.2 ≠ k₁ v.1 ∧ v.2 ≠ k₂ v.1

instance : DecidablePred (IsRest k₁ k₂) := fun v ↦ by unfold IsRest; infer_instance

/-- The substitution `X_{h, k₁} ↦ c_{h, k₁} X_{h, k₁} + c_{h, k₂} X_{h, k₂}`. -/
noncomputable def substL₂ (v : Fin m × ι) : MvPolynomial (Fin m × ι) ℚ :=
  if v.2 = k₁ v.1 then C (c v.1 (k₁ v.1)) * X v + C (c v.1 (k₂ v.1)) * X (v.1, k₂ v.1) else X v

/-- The inverse of `substL₂`. -/
noncomputable def substL₂Inv (v : Fin m × ι) : MvPolynomial (Fin m × ι) ℚ :=
  if v.2 = k₁ v.1 then C (c v.1 (k₁ v.1))⁻¹ * (X v - C (c v.1 (k₂ v.1)) * X (v.1, k₂ v.1))
  else X v

omit [Fintype ι] in
lemma aeval_substL₂Inv_substL₂ (hc : ∀ h, c h (k₁ h) ≠ 0) (hk : ∀ h, k₁ h ≠ k₂ h)
    (H : MvPolynomial (Fin m × ι) ℚ) :
    aeval (substL₂Inv c k₁ k₂) (aeval (substL₂ c k₁ k₂) H) = H := by
  rw [comp_aeval_apply]
  conv_rhs => rw [← aeval_X_left_apply H]
  refine congrArg (fun f ↦ aeval f H) (funext fun v ↦ ?_)
  by_cases hv : v.2 = k₁ v.1
  · have h2 : substL₂Inv c k₁ k₂ (v.1, k₂ v.1) = X (v.1, k₂ v.1) := by
      rw [substL₂Inv, ite_eq_right (show ¬ (k₂ v.1 = k₁ v.1) from (hk v.1).symm)]
    rw [substL₂, ite_eq_left hv]
    simp only [map_add, map_mul, aeval_C, aeval_X, algebraMap_eq, h2]
    rw [substL₂Inv, ite_eq_left hv, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc v.1), C_1, one_mul,
      sub_add_cancel]
  · simp [substL₂, substL₂Inv, hv]

lemma eval_aeval_eq {σ τ R : Type*} [CommRing R] (y : τ → R) (f : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) :
    MvPolynomial.eval y (aeval f p) = MvPolynomial.eval (fun v ↦ MvPolynomial.eval y (f v)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, aeval_X, hp, eval_X]

lemma eval_zeroOn' {σ R : Type*} [CommRing R] (S : σ → Prop) [DecidablePred S] (y : σ → R)
    (H : MvPolynomial σ R) :
    MvPolynomial.eval y (zeroOn S H) = MvPolynomial.eval (fun v ↦ if S v then 0 else y v) H := by
  rw [zeroOn, eval_aeval_eq]
  refine congrArg (fun f ↦ MvPolynomial.eval f H) (funext fun v ↦ ?_)
  split_ifs <;> simp

/-- The key identity of [schmidt1980], Chapter VI, pp. 192–193: if `κ` (an exponent in the
variables `X_{h k}`, `k ∉ {k₁, k₂}`) is of minimal degree such that the coefficient of `X ^ κ` in
`G = F(X_{h, k₁} ↦ (X_{h, k₁} - ∑_{k ≠ k₁} c_{h k} X_{h k}) / c_{h, k₁})` is non-zero, then the
coefficient of `X ^ κ` in `F` is obtained from the coefficient of `X ^ κ` in `G` by the
substitution `X_{h, k₁} ↦ c_{h, k₁} X_{h, k₁} + c_{h, k₂} X_{h, k₂}`. -/
lemma zeroOn_hasseDeriv_eq (hc : ∀ h, c h (k₁ h) ≠ 0) (hk : ∀ h, k₁ h ≠ k₂ h)
    (F : MvPolynomial (Fin m × ι) ℚ) (κ : Fin m × ι →₀ ℕ) (hκ : ∀ v ∈ κ.support, IsRest k₁ k₂ v)
    (hmin : ∀ κ' : Fin m × ι →₀ ℕ, (∀ v ∈ κ'.support, IsRest k₁ k₂ v) → κ'.degree < κ.degree →
      zeroOn (IsRest k₁ k₂) (hasseDeriv κ' (aeval (substLInv c k₁) F)) = 0) :
    zeroOn (IsRest k₁ k₂) (hasseDeriv κ F) = aeval (substL₂ c k₁ k₂)
      (zeroOn (IsRest k₁ k₂) (hasseDeriv κ (aeval (substLInv c k₁) F))) := by
  classical
  have hF : F = aeval (substL c k₁) (aeval (substLInv c k₁) F) :=
    (aeval_substL_substLInv c k₁ hc F).symm
  generalize aeval (substLInv c k₁) F = G at hmin hF ⊢
  refine MvPolynomial.funext fun y ↦ ?_
  set y₀ : Fin m × ι → ℚ := fun v ↦ if IsRest k₁ k₂ v then 0 else y v with hy₀
  set w : Fin m × ι → ℚ := fun v ↦ MvPolynomial.eval y₀ (substL c k₁ v) with hw
  have hw0 : ∀ v, IsRest k₁ k₂ v → w v = 0 := fun v hv ↦ by
    simp [hw, substL, hv.1, hy₀, hv]
  -- the right hand side
  have hR : MvPolynomial.eval y (aeval (substL₂ c k₁ k₂) (zeroOn (IsRest k₁ k₂) (hasseDeriv κ G)))
      = MvPolynomial.eval w (hasseDeriv κ G) := by
    rw [eval_aeval_eq, eval_zeroOn']
    refine congrArg (fun f ↦ MvPolynomial.eval f (hasseDeriv κ G)) (funext fun v ↦ ?_)
    by_cases hv : IsRest k₁ k₂ v
    · rw [ite_eq_left hv, hw0 v hv]
    · rw [ite_eq_right hv]
      by_cases h1 : v.2 = k₁ v.1
      · have hv' : v = (v.1, k₁ v.1) := Prod.ext rfl h1
        have h2 : ¬ IsRest k₁ k₂ (v.1, k₂ v.1) := fun h ↦ h.2 rfl
        have h3 : ¬ IsRest k₁ k₂ (v.1, k₁ v.1) := fun h ↦ h.1 rfl
        rw [hw]
        simp only [substL₂, substL, h1, ite_true, map_add, map_mul, eval_C, eval_X, map_sum]
        rw [Finset.sum_eq_add (k₁ v.1) (k₂ v.1) (hk v.1)
          (fun k _ hk' ↦ by simp [hy₀, IsRest, hk'.1, hk'.2]) (by simp) (by simp)]
        simp only [hy₀, ite_eq_right h2, ← hv', ite_eq_right hv]
      · have h2 : ¬ v.2 = k₁ v.1 := h1
        simp [hw, substL₂, substL, h2, hy₀, hv]
  rw [hR, eval_zeroOn']
  set L : Fin m × ι → MvPolynomial (Fin m × ι) ℚ := fun v ↦ if v.2 = k₁ v.1 then
      ∑ k, (if IsRest k₁ k₂ (v.1, k) then C (c v.1 k) * X (v.1, k) else 0)
    else if IsRest k₁ k₂ v then X v else 0 with hL
  have hκ' : ∀ v ∈ κ.support, ¬ ¬ IsRest k₁ k₂ v := fun v hv ↦ not_not.mpr (hκ v hv)
  have h4 : zeroOn (fun u ↦ ¬ IsRest k₁ k₂ u) (aeval (fun v ↦ C (y₀ v) + X v) F) =
      aeval L (aeval (fun v ↦ C (w v) + X v) G) := by
    rw [hF, comp_aeval_apply (φ := aeval fun v ↦ C (y₀ v) + X v),
      comp_aeval_apply (φ := zeroOn fun u ↦ ¬ IsRest k₁ k₂ u), comp_aeval_apply]
    refine congrArg (fun f ↦ aeval f G) (funext fun v ↦ ?_)
    simp only [map_add, aeval_C, aeval_X, algebraMap_eq]
    by_cases h1 : v.2 = k₁ v.1
    · have hwv : w v = ∑ k, c v.1 k * y₀ (v.1, k) := by simp [hw, substL, h1]
      rw [hwv, substL, ite_eq_left h1, hL]
      simp only [h1, ite_true, map_sum, map_mul, map_add, aeval_C, aeval_X, algebraMap_eq, zeroOn,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      by_cases hr : IsRest k₁ k₂ (v.1, k)
      · simp [hr]
        ring
      · simp [hr]
    · have hwv : w v = y₀ v := by simp [hw, substL, h1]
      rw [hwv, substL, ite_eq_right h1, hL]
      simp only [h1, ite_false, aeval_X, map_add, aeval_C, algebraMap_eq, zeroOn]
      by_cases hr : IsRest k₁ k₂ v <;> simp [hr]
  have hLS : ∀ v, IsRest k₁ k₂ v → L v = X v := fun v hv ↦ by
    simp [hL, hv, hv.1]
  have hLh : ∀ v, (L v).IsHomogeneous 1 := fun v ↦ by
    simp only [hL]
    split_ifs
    · exact IsHomogeneous.sum _ _ _ fun k _ ↦ by
        split_ifs
        · exact isHomogeneous_C_mul_X _ _
        · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_zero _ _ _
  have hweval : ∀ H : MvPolynomial (Fin m × ι) ℚ,
      MvPolynomial.eval w (zeroOn (IsRest k₁ k₂) H) = MvPolynomial.eval w H := fun H ↦ by
    rw [eval_zeroOn']
    refine congrArg (fun f ↦ MvPolynomial.eval f H) (funext fun v ↦ ?_)
    split_ifs with hv
    · exact (hw0 v hv).symm
    · rfl
  have hT : ∀ e ∈ (aeval (fun v ↦ C (w v) + X v) G).support,
      (∃ v ∈ e.support, ¬ IsRest k₁ k₂ v) → e.degree ≠ κ.degree := by
    rintro e he ⟨v, hv, hvR⟩ hdeg
    set eR := e.filter (IsRest k₁ k₂) with heR
    set eN := e.filter (fun u ↦ ¬ IsRest k₁ k₂ u) with heN
    have hsplit : e = eR + eN := by rw [heR, heN, Finsupp.filter_add_filter_not]
    have hN0 : eN ≠ 0 := fun h0 ↦ by
      have : eN v = 0 := by rw [h0]; rfl
      rw [heN, Finsupp.filter_apply_pos (fun u ↦ ¬ IsRest k₁ k₂ u) e hvR] at this
      exact Finsupp.mem_support_iff.mp hv this
    have hdegN : 0 < eN.degree := Nat.pos_of_ne_zero (mt (Finsupp.degree_eq_zero_iff eN).mp hN0)
    have hdegR : eR.degree < κ.degree := by
      have : e.degree = eR.degree + eN.degree := by rw [hsplit, map_add]
      omega
    have hR0 := hmin eR (fun u hu ↦ by
      rw [heR, Finsupp.support_filter, Finset.mem_filter] at hu
      exact hu.2) hdegR
    have hdisj : ∀ u, eR u = 0 ∨ eN u = 0 := fun u ↦ by
      by_cases hu : IsRest k₁ k₂ u
      · right
        rw [heN, Finsupp.filter_apply]
        simp [hu]
      · left
        rw [heR, Finsupp.filter_apply]
        simp [hu]
    have hNS : ∀ u ∈ eN.support, ¬ IsRest k₁ k₂ u := fun u hu ↦ by
      rw [heN, Finsupp.support_filter, Finset.mem_filter] at hu
      exact hu.2
    apply mem_support_iff.mp he
    rw [coeff_aeval_C_add_X, hsplit, ← hasseDeriv_hasseDeriv_of_disjoint hdisj, ← hweval,
      ← hasseDeriv_zeroOn _ hNS, hR0, hasseDeriv_zero_right, map_zero]
  calc MvPolynomial.eval y₀ (hasseDeriv κ F)
      = (aeval (fun v ↦ C (y₀ v) + X v) F).coeff κ := (coeff_aeval_C_add_X _ _ _).symm
    _ = (zeroOn (fun u ↦ ¬ IsRest k₁ k₂ u) (aeval (fun v ↦ C (y₀ v) + X v) F)).coeff κ := by
        rw [coeff_zeroOn, ite_eq_left hκ']
    _ = (aeval L (aeval (fun v ↦ C (w v) + X v) G)).coeff κ := by rw [h4]
    _ = (aeval (fun v ↦ C (w v) + X v) G).coeff κ :=
        coeff_aeval_of_isHomogeneous (IsRest k₁ k₂) L hLS hLh _ κ hT
    _ = MvPolynomial.eval w (hasseDeriv κ G) := coeff_aeval_C_add_X _ _ _

end Blocks2


section Dehom

variable {m : ℕ} {ι : Type*} [DecidableEq ι] (k₁ k₂ : Fin m → ι) {R : Type*} [CommRing R]

/-- Dehomogenisation: `X_{h, k₁} ↦ X_h`, `X_{h, k₂} ↦ 1`, the other variables `↦ 0`. -/
noncomputable def dehom (v : Fin m × ι) : MvPolynomial (Fin m) R :=
  if v.2 = k₁ v.1 then X v.1 else if v.2 = k₂ v.1 then 1 else 0

/-- The exponents of the variables `X_{h, k₁}`. -/
noncomputable def piK1 (a : Fin m × ι →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun h ↦ a (h, k₁ h)

omit [DecidableEq ι] in
@[simp] lemma piK1_apply (a : Fin m × ι →₀ ℕ) (h : Fin m) : piK1 k₁ a h = a (h, k₁ h) := rfl

variable [Fintype ι]

lemma aeval_dehom_monomial (a : Fin m × ι →₀ ℕ) (ha : ∀ v ∈ a.support, ¬ IsRest k₁ k₂ v)
    (r : R) : aeval (dehom k₁ k₂) (monomial a r) = monomial (piK1 k₁ a) r := by
  classical
  rw [aeval_monomial, algebraMap_eq, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
  congr 1
  refine Finset.prod_congr rfl fun h _ ↦ ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (k₁ h))]
  rw [Finset.prod_eq_one fun k hk ↦ ?_]
  · simp [dehom]
  · by_cases hk2 : k = k₂ h
    · simp only [dehom]
      rw [ite_eq_right (Finset.ne_of_mem_erase hk), ite_eq_left hk2, one_pow]
    · have hr : IsRest k₁ k₂ (h, k) := ⟨Finset.ne_of_mem_erase hk, hk2⟩
      have : a (h, k) = 0 := by
        by_contra h0
        exact ha _ (Finsupp.mem_support_iff.mpr h0) hr
      simp [this]

lemma coeff_aeval_dehom (H : MvPolynomial (Fin m × ι) R)
    (hH : ∀ a ∈ H.support, ∀ v ∈ a.support, ¬ IsRest k₁ k₂ v) (j : Fin m →₀ ℕ) :
    (aeval (dehom k₁ k₂) H).coeff j =
      ∑ a ∈ H.support, if piK1 k₁ a = j then H.coeff a else 0 := by
  classical
  conv_lhs => rw [H.as_sum]
  rw [map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [aeval_dehom_monomial k₁ k₂ a (hH a ha), coeff_monomial]

lemma map_zeroOn {σ R' : Type*} [CommRing R'] (f : R →+* R') (S : σ → Prop) [DecidablePred S]
    (H : MvPolynomial σ R) : map f (zeroOn S H) = zeroOn S (map f H) := by
  ext a
  rw [coeff_map, coeff_zeroOn, coeff_zeroOn, coeff_map]
  split_ifs <;> simp

omit [Fintype ι] in
lemma map_aeval_dehom {R' : Type*} [CommRing R'] (f : R →+* R') (H : MvPolynomial (Fin m × ι) R) :
    map f (aeval (dehom k₁ k₂) H) = aeval (dehom k₁ k₂) (map f H) := by
  induction H using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, aeval_X, map_X]
    congr 1
    simp only [dehom]
    split_ifs <;> simp

lemma exists_of_coeff_aeval_dehom_ne_zero (H : MvPolynomial (Fin m × ι) R)
    (hH : ∀ a ∈ H.support, ∀ v ∈ a.support, ¬ IsRest k₁ k₂ v) (j : Fin m →₀ ℕ)
    (hj : (aeval (dehom (R := R) k₁ k₂) H).coeff j ≠ 0) :
    ∃ a ∈ H.support, piK1 k₁ a = j := by
  classical
  rw [coeff_aeval_dehom k₁ k₂ H hH] at hj
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj
  refine ⟨a, ha, ?_⟩
  by_contra h
  exact hne (ite_eq_right h)

lemma coeff_aeval_dehom_piK1 (H : MvPolynomial (Fin m × ι) R)
    (hH : ∀ a ∈ H.support, ∀ v ∈ a.support, ¬ IsRest k₁ k₂ v)
    (hinj : ∀ a ∈ H.support, ∀ b ∈ H.support, piK1 k₁ a = piK1 k₁ b → a = b)
    (a : Fin m × ι →₀ ℕ) (ha : a ∈ H.support) :
    (aeval (dehom (R := R) k₁ k₂) H).coeff (piK1 k₁ a) = H.coeff a := by
  classical
  rw [coeff_aeval_dehom k₁ k₂ H hH, Finset.sum_eq_single a, ite_eq_left rfl]
  · intro b hb hba
    exact ite_eq_right fun h ↦ hba (hinj b hb a ha h)
  · intro h
    exact absurd ha h

end Dehom

variable {ι : Type*} [Fintype ι]

/-- If `d_k` divides `A` for every `k ∈ s`, then `∏ d_k` divides `A ^ (|s| - 1) gcd(d_k)`. -/
lemma prod_dvd_pow_mul_gcd {ι : Type*} [DecidableEq ι] (d : ι → ℕ) (A : ℕ) (s : Finset ι)
    (hs : s.Nonempty) (hd : ∀ k ∈ s, d k ∣ A) :
    ∏ k ∈ s, d k ∣ A ^ (s.card - 1) * s.gcd d := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton k => simp
  | cons j s hj hs ih =>
    rw [Finset.prod_cons, Finset.card_cons, Finset.cons_eq_insert, Finset.gcd_insert]
    have ih' := ih fun k hk ↦ hd k (Finset.mem_cons_of_mem hk)
    have hdj : d j ∣ A := hd j (Finset.mem_cons_self j s)
    obtain ⟨k, hk⟩ := hs
    have hg : s.gcd d ∣ A := (Finset.gcd_dvd hk).trans (hd k (Finset.mem_cons_of_mem hk))
    have hl : Nat.lcm (d j) (s.gcd d) ∣ A := Nat.lcm_dvd hdj hg
    have h1 : d j * s.gcd d ∣ A * Nat.gcd (d j) (s.gcd d) := by
      rw [← Nat.gcd_mul_lcm, mul_comm (Nat.gcd _ _)]
      exact Nat.mul_dvd_mul_right hl _
    have h2 : s.card + 1 - 1 = (s.card - 1) + 1 := by
      have : 0 < s.card := Finset.card_pos.mpr ⟨k, hk⟩
      omega
    rw [h2, pow_succ]
    calc d j * ∏ k ∈ s, d k ∣ d j * (A ^ (s.card - 1) * s.gcd d) := Nat.mul_dvd_mul_left _ ih'
      _ = A ^ (s.card - 1) * (d j * s.gcd d) := by ring
      _ ∣ A ^ (s.card - 1) * (A * Nat.gcd (d j) (s.gcd d)) := Nat.mul_dvd_mul_left _ h1
      _ = A ^ (s.card - 1) * A * Nat.gcd (d j) (s.gcd d) := by ring

/-- [schmidt1980], Chapter VI, Lemma 10A: if `c₁, …, cₙ` are coprime integers with `c_{k₁} ≠ 0`
and `n ≥ 2`, there is `k₂ ≠ k₁` with `gcd(c_{k₁}, c_{k₂}) ≤ |c_{k₁}| ^ ((n - 2) / (n - 1))`. -/
theorem exists_gcd_le_rpow (hn : 2 ≤ Fintype.card ι) (c : ι → ℤ)
    (hc : Finset.univ.gcd c = 1) (k₁ : ι) (hk₁ : c k₁ ≠ 0) :
    ∃ k₂, k₂ ≠ k₁ ∧ (Int.gcd (c k₁) (c k₂) : ℝ) ≤
      |(c k₁ : ℝ)| ^ (((Fintype.card ι : ℝ) - 2) / ((Fintype.card ι : ℝ) - 1)) := by
  classical
  set s := Finset.univ.erase k₁ with hs
  have hcard : s.card = Fintype.card ι - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _)]
    rfl
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  set d : ι → ℕ := fun k ↦ Int.gcd (c k₁) (c k) with hd
  set A := (c k₁).natAbs with hA
  have hA0 : 0 < A := Int.natAbs_pos.mpr hk₁
  have hdA : ∀ k ∈ s, d k ∣ A := fun k _ ↦ Int.gcd_dvd_natAbs_left _ _
  have hgcd : s.gcd d = 1 := by
    have h1 : ((s.gcd d : ℕ) : ℤ) ∣ Finset.univ.gcd c := by
      refine Finset.dvd_gcd fun k _ ↦ ?_
      by_cases hk : k = k₁
      · subst hk
        obtain ⟨j, hj⟩ := hsne
        exact (Int.natCast_dvd_natCast.mpr (Finset.gcd_dvd hj)).trans (Int.gcd_dvd_left _ _)
      · exact (Int.natCast_dvd_natCast.mpr
          (Finset.gcd_dvd (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩))).trans
          (Int.gcd_dvd_right _ _)
    rw [hc] at h1
    exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1
  have hprod := prod_dvd_pow_mul_gcd d A s hsne hdA
  rw [hgcd, mul_one, hcard] at hprod
  have hle : ∏ k ∈ s, d k ≤ A ^ (Fintype.card ι - 1 - 1) := Nat.le_of_dvd (by positivity) hprod
  obtain ⟨k₂, hk₂, hmin⟩ := Finset.exists_min_image s d hsne
  have hpow : d k₂ ^ (Fintype.card ι - 1) ≤ A ^ (Fintype.card ι - 2) := by
    rw [← hcard]
    calc d k₂ ^ s.card ≤ ∏ k ∈ s, d k := Finset.pow_card_le_prod _ _ _ hmin
      _ ≤ _ := by rw [show Fintype.card ι - 2 = Fintype.card ι - 1 - 1 by omega]; exact hle
  refine ⟨k₂, (Finset.mem_erase.mp hk₂).1, ?_⟩
  have hN : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
    linarith
  have hAabs : |(c k₁ : ℝ)| = (A : ℝ) := by rw [hA, Nat.cast_natAbs, Int.cast_abs]
  rw [hAabs]
  have hpowR : ((d k₂ : ℝ)) ^ ((Fintype.card ι : ℝ) - 1) ≤
      (A : ℝ) ^ ((Fintype.card ι : ℝ) - 2) := by
    have h1 : ((Fintype.card ι : ℝ) - 1) = ((Fintype.card ι - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; simp
    have h2 : ((Fintype.card ι : ℝ) - 2) = ((Fintype.card ι - 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hn]; simp
    rw [h1, h2, Real.rpow_natCast, Real.rpow_natCast]
    exact_mod_cast hpow
  calc (d k₂ : ℝ)
        = ((d k₂ : ℝ) ^ ((Fintype.card ι : ℝ) - 1)) ^ (1 / ((Fintype.card ι : ℝ) - 1)) := by
        rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hN.ne', Real.rpow_one]
    _ ≤ ((A : ℝ) ^ ((Fintype.card ι : ℝ) - 2)) ^ (1 / ((Fintype.card ι : ℝ) - 1)) :=
        Real.rpow_le_rpow (by positivity) hpowR (by positivity)
    _ = _ := by rw [← Real.rpow_mul (by positivity)]; ring_nf

/-- The reduction to one variable per block ([schmidt1980], Chapter VI, pp. 192–194, and
Lemma 4C). Let `P ≠ 0` be block homogeneous of degree `d`, let `V_h` be the hyperplane
`c_h ⬝ X_h = 0` and let `k₁ h ≠ k₂ h` be coordinates with `c_{h, k₁} ≠ 0`. Then there is a
polynomial `Q ≠ 0` in one variable per block, of degree at most `d_h` in `X_h`, with
`|Q| ≤ |P|`, such that whenever the divided derivative `Q_j` does not vanish at the point
`α_h = -c_{h, k₂} / c_{h, k₁}`, there are a rational point `x ∈ V₁ × ⋯ × Vₘ` and a multi-index
`i` with `(i / d) = (j / d)` and `P_i(x) ≠ 0`.

The polynomial `Q` is obtained from `P` by taking the coefficient of the lowest power
`X^κ` of the variables `X_{h k}`, `k ∉ {k₁ h, k₂ h}`, with respect to coordinates adapted to the
`V_h`, and then putting `X_{h, k₂} = 1`. -/
theorem exists_reduction {m : ℕ} (P : MvPolynomial (Fin m × ι) ℤ) (hP : P ≠ 0)
    (d : Fin m → ℕ) (hhom : IsBlockHomogeneous P d) (c : Fin m → ι → ℤ) (k₁ k₂ : Fin m → ι)
    (hk : ∀ h, k₁ h ≠ k₂ h) (hc : ∀ h, c h (k₁ h) ≠ 0) :
    ∃ Q : MvPolynomial (Fin m) ℤ, Q ≠ 0 ∧ (∀ h, Q.degreeOf h ≤ d h) ∧ height Q ≤ height P ∧
      ∀ j : Fin m →₀ ℕ, MvPolynomial.eval (fun h ↦ -(c h (k₂ h) : ℚ) / c h (k₁ h))
          (map (Int.castRingHom ℚ) (hasseDeriv j Q)) ≠ 0 →
        ∃ x : Fin m → ι → ℚ, (∀ h, ∑ k, (c h k : ℚ) * x h k = 0) ∧
          ∃ i : Fin m × ι →₀ ℕ, blockWeight d i = rothWeight d j ∧
            MvPolynomial.eval (fun p ↦ x p.1 p.2)
              (map (Int.castRingHom ℚ) (hasseDeriv i P)) ≠ 0 := by
  classical
  set cq : Fin m → ι → ℚ := fun h k ↦ (c h k : ℚ) with hcq
  have hcq0 : ∀ h, cq h (k₁ h) ≠ 0 := fun h ↦ by simp [hcq, hc h]
  set F := map (Int.castRingHom ℚ) P with hFdef
  have hF0 : F ≠ 0 := by
    intro h0
    apply hP
    exact map_injective _ Int.cast_injective (by rw [← hFdef, h0, map_zero])
  set G := aeval (substLInv cq k₁) F with hG
  have hG0 : G ≠ 0 := by
    intro h0
    apply hF0
    rw [← aeval_substL_substLInv cq k₁ hcq0 F, ← hG, h0, map_zero]
  -- the exponent `κ` of minimal degree
  have hex : ∃ n, ∃ κ : Fin m × ι →₀ ℕ, (∀ v ∈ κ.support, IsRest k₁ k₂ v) ∧ κ.degree = n ∧
      zeroOn (IsRest k₁ k₂) (hasseDeriv κ G) ≠ 0 := by
    obtain ⟨e, he⟩ := ne_zero_iff.mp hG0
    refine ⟨_, e.filter (IsRest k₁ k₂), fun v hv ↦ ?_, rfl, fun h0 ↦ ?_⟩
    · rw [Finsupp.support_filter, Finset.mem_filter] at hv
      exact hv.2
    · have := coeff_zeroOn_hasseDeriv_filter (IsRest k₁ k₂) e G
      rw [h0] at this
      exact he (by simpa using this.symm)
  obtain ⟨κ, hκR, hκdeg, hκ0⟩ := Nat.find_spec hex
  have hmin : ∀ κ' : Fin m × ι →₀ ℕ, (∀ v ∈ κ'.support, IsRest k₁ k₂ v) →
      κ'.degree < κ.degree → zeroOn (IsRest k₁ k₂) (hasseDeriv κ' G) = 0 := by
    intro κ' h1 h2
    by_contra h3
    exact Nat.find_min hex (hκdeg ▸ h2) ⟨κ', h1, rfl, h3⟩
  have hid := zeroOn_hasseDeriv_eq cq k₁ k₂ hcq0 hk F κ hκR hmin
  rw [← hG] at hid
  set G' := zeroOn (IsRest k₁ k₂) (hasseDeriv κ G) with hG'
  have hG'supp : ∀ a ∈ G'.support, ∀ v ∈ a.support, ¬ IsRest k₁ k₂ v := fun a ha v hv hr ↦ by
    have := mem_support_iff.mp ha
    rw [hG', coeff_zeroOn, ite_eq_right (fun h ↦ h v hv hr)] at this
    exact this rfl
  -- the integer polynomial `H` and the polynomial `Q`
  set H := zeroOn (IsRest k₁ k₂) (hasseDeriv κ P) with hH
  have hHmap : map (Int.castRingHom ℚ) H = aeval (substL₂ cq k₁ k₂) G' := by
    rw [hH, map_zeroOn, map_hasseDeriv, ← hFdef, hid]
  have hH0 : H ≠ 0 := fun h0 ↦ hκ0 (by
    have := congrArg (aeval (substL₂Inv cq k₁ k₂)) hHmap
    rw [aeval_substL₂Inv_substL₂ cq k₁ k₂ hcq0 hk, h0, map_zero, map_zero] at this
    exact this.symm)
  have hHsupp : ∀ a ∈ H.support, ∀ v ∈ a.support, ¬ IsRest k₁ k₂ v := fun a ha v hv hr ↦ by
    have := mem_support_iff.mp ha
    rw [hH, coeff_zeroOn, ite_eq_right (fun h ↦ h v hv hr)] at this
    exact this rfl
  have hκa : ∀ a ∈ H.support, ∀ v ∈ κ.support, a v = 0 := fun a ha v hv ↦ by
    by_contra h0
    exact hHsupp a ha v (Finsupp.mem_support_iff.mpr h0) (hκR v hv)
  have hHcoeff : ∀ a ∈ H.support, H.coeff a = P.coeff (a + κ) := fun a ha ↦ by
    rw [hH, coeff_zeroOn, ite_eq_left (hHsupp a ha), coeff_hasseDeriv_of_disjoint (hκa a ha)]
  have hHhom : ∀ a ∈ H.support, ∀ h, ∑ k, a (h, k) = d h - ∑ k, κ (h, k) := fun a ha h ↦ by
    have h1 : (hasseDeriv κ P).coeff a ≠ 0 := by
      have := mem_support_iff.mp ha
      rwa [hH, coeff_zeroOn, ite_eq_left (hHsupp a ha)] at this
    exact (hhom.hasseDeriv κ).sum_eq h1 h
  have hsum2 : ∀ a ∈ H.support, ∀ h, ∑ k, a (h, k) = a (h, k₁ h) + a (h, k₂ h) := fun a ha h ↦ by
    refine Finset.sum_eq_add (k₁ h) (k₂ h) (hk h) (fun k _ hk' ↦ ?_) (by simp) (by simp)
    by_contra h0
    exact hHsupp a ha (h, k) (Finsupp.mem_support_iff.mpr h0) ⟨hk'.1, hk'.2⟩
  have hinj : ∀ a ∈ H.support, ∀ b ∈ H.support, piK1 k₁ a = piK1 k₁ b → a = b := by
    intro a ha b hb hab
    ext ⟨h, k⟩
    have h1 : a (h, k₁ h) = b (h, k₁ h) := by
      have := congrArg (fun f ↦ f h) hab
      simpa using this
    by_cases hk1 : k = k₁ h
    · rw [hk1, h1]
    by_cases hk2 : k = k₂ h
    · have h2 := hHhom a ha h
      have h3 := hHhom b hb h
      rw [hsum2 a ha h] at h2
      rw [hsum2 b hb h] at h3
      rw [hk2]
      omega
    · have hr : IsRest k₁ k₂ (h, k) := ⟨hk1, hk2⟩
      have ha0 : a (h, k) = 0 := by
        by_contra h0
        exact hHsupp a ha _ (Finsupp.mem_support_iff.mpr h0) hr
      have hb0 : b (h, k) = 0 := by
        by_contra h0
        exact hHsupp b hb _ (Finsupp.mem_support_iff.mpr h0) hr
      rw [ha0, hb0]
  set Q : MvPolynomial (Fin m) ℤ := aeval (dehom k₁ k₂) H with hQ
  have hQex : ∀ j, Q.coeff j ≠ 0 → ∃ a ∈ H.support, piK1 k₁ a = j ∧ Q.coeff j = H.coeff a := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := exists_of_coeff_aeval_dehom_ne_zero k₁ k₂ H hHsupp j hj
    exact ⟨a, ha, rfl, coeff_aeval_dehom_piK1 k₁ k₂ H hHsupp hinj a ha⟩
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := ne_zero_iff.mp hH0
    intro h0
    have := coeff_aeval_dehom_piK1 k₁ k₂ H hHsupp hinj a (mem_support_iff.mpr ha)
    rw [← hQ, h0] at this
    exact ha (by simpa using this.symm)
  · intro h
    rw [degreeOf_le_iff]
    intro j hj
    obtain ⟨a, ha, rfl, -⟩ := hQex j (mem_support_iff.mp hj)
    have h1 := hHhom a ha h
    rw [hsum2 a ha h] at h1
    simp only [piK1_apply]
    omega
  · refine Finset.sup_le fun j hj ↦ ?_
    obtain ⟨a, ha, -, hja⟩ := hQex j (mem_support_iff.mp hj)
    rw [hja, hHcoeff a ha]
    have hmem : a + κ ∈ P.support := by
      rw [mem_support_iff, ← hHcoeff a ha]
      exact mem_support_iff.mp ha
    exact Finset.le_sup (f := fun j ↦ (P.coeff j).natAbs) hmem
  · intro j hj
    set α : Fin m → ℚ := fun h ↦ -(c h (k₂ h) : ℚ) / c h (k₁ h) with hα
    rw [map_hasseDeriv, ← coeff_aeval_C_add_X, hQ, map_aeval_dehom, hHmap] at hj
    have hper : aeval (fun h ↦ C (α h) + X h)
        (aeval (dehom (R := ℚ) k₁ k₂) (aeval (substL₂ cq k₁ k₂) G')) =
        aeval (fun h ↦ C (cq h (k₁ h)) * X h) (aeval (dehom (R := ℚ) k₁ k₂) G') := by
      rw [comp_aeval_apply (φ := aeval (dehom (R := ℚ) k₁ k₂)), comp_aeval_apply,
        comp_aeval_apply]
      refine congrArg (fun f ↦ aeval f G') (funext fun v ↦ ?_)
      by_cases h1 : v.2 = k₁ v.1
      · have hd1 : dehom k₁ k₂ v = (X v.1 : MvPolynomial (Fin m) ℚ) := by simp [dehom, h1]
        have hd2 : dehom k₁ k₂ (v.1, k₂ v.1) = (1 : MvPolynomial (Fin m) ℚ) := by
          simp [dehom, (hk v.1).symm]
        have hαv : cq v.1 (k₁ v.1) * α v.1 + cq v.1 (k₂ v.1) = 0 := by
          have hc1 : (c v.1 (k₁ v.1) : ℚ) ≠ 0 := by exact_mod_cast hc v.1
          simp only [hcq, hα]
          rw [mul_div_assoc', mul_neg, mul_comm, neg_div, mul_div_assoc, div_self hc1, mul_one,
            neg_add_cancel]
        rw [substL₂, ite_eq_left h1]
        simp only [map_add, map_mul, aeval_C, aeval_X, algebraMap_eq, hd1, hd2, mul_one]
        rw [mul_add, add_assoc, add_comm (C (cq v.1 (k₁ v.1)) * X v.1), ← add_assoc, ← C_mul,
          ← C_add, hαv, C_0, zero_add]
      · rw [substL₂, ite_eq_right h1, aeval_X]
        simp only [dehom, h1, ite_false]
        split_ifs <;> simp
    rw [hper, coeff_aeval_C_mul_X] at hj
    have hj2 := right_ne_zero_of_mul hj
    obtain ⟨a, ha, haj⟩ := exists_of_coeff_aeval_dehom_ne_zero k₁ k₂ G' hG'supp j hj2
    have hκa' : ∀ v ∈ κ.support, a v = 0 := fun v hv ↦ by
      by_contra h0
      exact hG'supp a ha v (Finsupp.mem_support_iff.mpr h0) (hκR v hv)
    have hE : G.coeff (a + κ) ≠ 0 := by
      have := mem_support_iff.mp ha
      rwa [hG', coeff_zeroOn, ite_eq_left (hG'supp a ha), coeff_hasseDeriv_of_disjoint hκa'] at this
    obtain ⟨z, hzV, hz⟩ := exists_point_of_coeff_ne_zero cq k₁ hcq0 F (a + κ) hE
    refine ⟨fun h k ↦ z (h, k), hzV, (a + κ).filter (fun v ↦ v.2 = k₁ v.1), ?_, ?_⟩
    · unfold blockWeight rothWeight
      refine Finset.sum_congr rfl fun h _ ↦ ?_
      congr 1
      have hκ1 : κ (h, k₁ h) = 0 := by
        by_contra h0
        exact (hκR _ (Finsupp.mem_support_iff.mpr h0)).1 rfl
      rw [← haj]
      simp [Finsupp.filter_apply, Finset.sum_add_distrib, hκ1]
    · rw [map_hasseDeriv]
      exact hz

/-- The point `-b / a` written in lowest terms `p / q` with `q > 0`; then `q gcd(a, b) = |a|`. -/
lemma exists_rat_eq_neg_div (a b : ℤ) (ha : a ≠ 0) :
    ∃ (p : ℤ) (q : ℕ), 0 < q ∧ IsCoprime p (q : ℤ) ∧ (p : ℚ) / q = -(b : ℚ) / a ∧
      (q : ℤ) * Int.gcd a b = |a| := by
  set r : ℚ := Rat.divInt (-b) a with hr
  refine ⟨r.num, r.den, r.den_pos, ?_, ?_, ?_⟩
  · rw [Int.isCoprime_iff_gcd_eq_one]
    exact r.reduced
  · rw [Rat.num_div_den, hr, Rat.divInt_eq_div]
    push_cast
    ring
  · rw [hr, Rat.den_divInt]
    simp only [ha, ↓reduceIte, Int.gcd_neg]
    have hd : Int.gcd a b ∣ a.natAbs := Int.gcd_dvd_natAbs_left a b
    rw [← Nat.cast_mul, Nat.div_mul_cancel hd, Int.natCast_natAbs]

/-- The sup norm of a non-zero integer vector is attained at some coordinate. -/
lemma exists_norm_eq_abs [Nonempty ι] (c : ι → ℤ) : ∃ k, ‖c‖ = |(c k : ℝ)| := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun b ↦ ‖c b‖₊)
  refine ⟨k, ?_⟩
  rw [Pi.norm_def, hk, coe_nnNorm, Int.norm_eq_abs]

/-- **Schmidt's generalisation of Roth's lemma** ([evertse1993], Proposition 3.4.2).
Let `0 < σ < 1`. There are positive constants `C₁`, `C₂`, `C₃` with the following property.
Let `0 < γ ≤ n - 1`, let `d₁, …, dₘ` be positive integers, let `V₁, …, Vₘ` be hyperplanes of
`ℚⁿ`, where `V_h` is defined by the equation `c_h ⬝ X = 0` for a primitive integer vector `c_h`,
so that `H(V_h) = ‖c_h‖`, and let `P` be a non-zero polynomial with integer coefficients which is
homogeneous of degree `d_h` in the block `X_h`. Assume that

* `d_h / d_{h + 1} ≥ C₁`;
* `H(V_h) ^ d_h ≥ H(V₁) ^ (γ d₁)` for `h ≠ 1`;
* `H(V_h) ≥ C₂ ^ ((n - 1) ^ 2 / γ)`;
* `H(P) ≤ H(V₁) ^ (C₃ γ d₁ / (n - 1) ^ 2)`.

Then there is a point `x ∈ V₁ × ⋯ × Vₘ` at which the index of `P` with respect to `d` is less than
`m σ`, i.e. there is `i` with `(i / d) < m σ` and `P_i(x) ≠ 0`. -/
theorem generalized_roth_lemma (ι : Type*) [Fintype ι] (hn : 2 ≤ Fintype.card ι)
    (m : ℕ) [NeZero m] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 1 < C₂ ∧ 0 < C₃ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ Fintype.card ι - 1 →
      ∀ d : Fin m → ℕ, (∀ h, 0 < d h) →
        (∀ h h' : Fin m, (h : ℕ) + 1 = h' → C₁ * d h' ≤ d h) →
      ∀ c : Fin m → ι → ℤ, (∀ h, Finset.univ.gcd (c h) = 1) →
        (∀ h, h ≠ 0 → ‖c 0‖ ^ (γ * d 0) ≤ ‖c h‖ ^ (d h : ℝ)) →
        (∀ h, C₂ ^ (((Fintype.card ι : ℝ) - 1) ^ 2 / γ) ≤ ‖c h‖) →
      ∀ P : MvPolynomial (Fin m × ι) ℤ, P ≠ 0 → IsBlockHomogeneous P d →
        (height P : ℝ) ≤ ‖c 0‖ ^ (C₃ * γ * d 0 / ((Fintype.card ι : ℝ) - 1) ^ 2) →
        ∃ x : Fin m → ι → ℚ, (∀ h, ∑ k, (c h k : ℚ) * x h k = 0) ∧
          ∃ i : Fin m × ι →₀ ℕ, blockWeight d i < m * σ ∧
            MvPolynomial.eval (fun p ↦ x p.1 p.2)
              (MvPolynomial.map (Int.castRingHom ℚ) (hasseDeriv i P)) ≠ 0 := by
  classical
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  set ε : ℝ := min (m * σ) (1 / 12) / 2 with hεdef
  have hmin : 0 < min (m * σ) (1 / 12) := lt_min (by positivity) (by norm_num)
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 / 12 := by
    have := min_le_right (m * σ) (1 / 12 : ℝ)
    linarith
  have hεσ : ε < m * σ := by
    have := min_le_left (m * σ) (1 / 12 : ℝ)
    linarith
  set ω := rothOmega m ε with hωdef
  have hω : 0 < ω := rothOmega_pos m hε0
  refine ⟨1 / ω, 2 ^ (3 * m / ω), ω, by positivity,
    Real.one_lt_rpow (by norm_num) (by positivity), hω, ?_⟩
  intro γ hγ hγn d hd hC₁ c hc hcH hC₂ P hP hhom hheight
  set N : ℝ := (Fintype.card ι : ℝ) - 1 with hNdef
  have hN : 1 ≤ N := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
    linarith
  have hN0 : 0 < N := by linarith
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  -- the coordinates `k₁ h`, `k₂ h` and the rational numbers `p_h / q_h`
  have hc0 : ∀ h, c h ≠ 0 := fun h h0 ↦ by
    have := hc h
    rw [h0, (Finset.gcd_eq_zero_iff (s := Finset.univ) (f := (0 : ι → ℤ))).mpr
      (fun _ _ ↦ rfl)] at this
    exact zero_ne_one this
  choose k₁ hk₁ using fun h ↦ exists_norm_eq_abs (c h)
  have hck₁ : ∀ h, c h (k₁ h) ≠ 0 := fun h h0 ↦ hc0 h (by
    have h1 : ‖c h‖ = 0 := by rw [hk₁ h, h0]; simp
    exact norm_eq_zero.mp h1)
  choose k₂ hk₂ hgcd using fun h ↦ exists_gcd_le_rpow hn (c h) (hc h) (k₁ h) (hck₁ h)
  choose p q hq hpq hpqα hqg using fun h ↦ exists_rat_eq_neg_div (c h (k₁ h)) (c h (k₂ h))
    (hck₁ h)
  -- elementary facts on `q_h`
  have hA1 : ∀ h, 1 ≤ ‖c h‖ := fun h ↦ by
    rw [hk₁ h]
    have : (1 : ℤ) ≤ |c h (k₁ h)| := Int.one_le_abs (hck₁ h)
    exact_mod_cast this
  have hq1 : ∀ h, (1 : ℝ) ≤ q h := fun h ↦ by exact_mod_cast hq h
  have hqA : ∀ h, (q h : ℝ) ≤ ‖c h‖ := fun h ↦ by
    have hg : 1 ≤ Int.gcd (c h (k₁ h)) (c h (k₂ h)) :=
      Nat.pos_of_ne_zero (Int.gcd_ne_zero_left (hck₁ h))
    have h1 : ((q h : ℤ) : ℝ) * (Int.gcd (c h (k₁ h)) (c h (k₂ h)) : ℤ) =
        ((|c h (k₁ h)| : ℤ) : ℝ) := by exact_mod_cast hqg h
    push_cast at h1
    rw [hk₁ h, ← h1]
    have : (1 : ℝ) ≤ (Int.gcd (c h (k₁ h)) (c h (k₂ h)) : ℝ) := by exact_mod_cast hg
    nlinarith [hq1 h]
  have hAq : ∀ h, ‖c h‖ ^ (1 / N) ≤ q h := fun h ↦ by
    have h1 : ((q h : ℤ) : ℝ) * (Int.gcd (c h (k₁ h)) (c h (k₂ h)) : ℤ) =
        ((|c h (k₁ h)| : ℤ) : ℝ) := by exact_mod_cast hqg h
    push_cast at h1
    have hg := hgcd h
    rw [hk₁ h]
    set A := |(c h (k₁ h) : ℝ)| with hA
    have hA0 : 0 < A := abs_pos.mpr (by exact_mod_cast hck₁ h)
    have hgpos : (0 : ℝ) < Int.gcd (c h (k₁ h)) (c h (k₂ h)) := by
      exact_mod_cast Nat.pos_of_ne_zero (Int.gcd_ne_zero_left (hck₁ h))
    have hsplit : A = A ^ (1 / N) * A ^ (((Fintype.card ι : ℝ) - 2) / N) := by
      rw [← Real.rpow_add hA0]
      have : 1 / N + ((Fintype.card ι : ℝ) - 2) / N = 1 := by
        field_simp
        rw [hNdef]
        ring
      rw [this, Real.rpow_one]
    have h2 : q h * (Int.gcd (c h (k₁ h)) (c h (k₂ h)) : ℝ) ≤
        q h * A ^ (((Fintype.card ι : ℝ) - 2) / N) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    have h3 : A ^ (1 / N) * A ^ (((Fintype.card ι : ℝ) - 2) / N) ≤
        q h * A ^ (((Fintype.card ι : ℝ) - 2) / N) := by
      calc A ^ (1 / N) * A ^ (((Fintype.card ι : ℝ) - 2) / N) = A := hsplit.symm
        _ = q h * (Int.gcd (c h (k₁ h)) (c h (k₂ h)) : ℝ) := h1.symm
        _ ≤ _ := h2
    exact le_of_mul_le_mul_right h3 (by positivity)
  -- the polynomial in one variable per block
  obtain ⟨Q, hQ0, hQdeg, hQH, hQred⟩ := exists_reduction P hP d hhom c k₁ k₂
    (fun h ↦ (hk₂ h).symm) hck₁
  -- the hypotheses of Roth's lemma, with `γ / (n - 1)` in place of `γ`
  set γ' := γ / N with hγ'
  have hγ'0 : 0 < γ' := by positivity
  have hγ'1 : γ' ≤ 1 := by rw [hγ', div_le_one hN0]; exact hγn
  have hR1 : ∀ h h' : Fin m, (h : ℕ) + 1 = h' → (d h' : ℝ) ≤ ω * d h := fun h h' hh ↦ by
    have := hC₁ h h' hh
    rw [one_div, inv_mul_le_iff₀ hω] at this
    exact this
  have hR2 : ∀ h, (q 0 : ℝ) ^ (γ' * d 0) ≤ (q h : ℝ) ^ (d h : ℝ) := by
    intro h
    by_cases h0 : h = 0
    · subst h0
      refine Real.rpow_le_rpow_of_exponent_le (hq1 0) ?_
      have : (0 : ℝ) ≤ d 0 := by positivity
      nlinarith
    · calc (q 0 : ℝ) ^ (γ' * d 0) ≤ ‖c 0‖ ^ (γ' * d 0) :=
            Real.rpow_le_rpow (by positivity) (hqA 0) (by positivity)
        _ = (‖c 0‖ ^ (γ * d 0)) ^ (1 / N) := by
            rw [← Real.rpow_mul (by positivity)]
            congr 1
            rw [hγ']
            ring
        _ ≤ (‖c h‖ ^ (d h : ℝ)) ^ (1 / N) :=
            Real.rpow_le_rpow (by positivity) (hcH h h0) (by positivity)
        _ = (‖c h‖ ^ (1 / N)) ^ (d h : ℝ) := by
            rw [← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_comm]
        _ ≤ (q h : ℝ) ^ (d h : ℝ) :=
            Real.rpow_le_rpow (by positivity) (hAq h) (by positivity)
  have hR3 : ∀ h, (2 : ℝ) ^ (3 * m) ≤ (q h : ℝ) ^ (ω * γ') := by
    intro h
    calc (2 : ℝ) ^ (3 * m) = ((2 : ℝ) ^ (3 * m / ω)) ^ (N ^ 2 / γ * (ω * γ' / N)) := by
          rw [← Real.rpow_mul (by norm_num)]
          have : 3 * (m : ℝ) / ω * (N ^ 2 / γ * (ω * γ' / N)) = 3 * m := by
            rw [hγ']
            field_simp
          rw [this]
          norm_cast
      _ = (((2 : ℝ) ^ (3 * m / ω)) ^ (N ^ 2 / γ)) ^ (ω * γ' / N) := by
          rw [← Real.rpow_mul (Real.rpow_nonneg (by norm_num) _), ← Real.rpow_mul (by norm_num)]
      _ ≤ ‖c h‖ ^ (ω * γ' / N) := Real.rpow_le_rpow (by positivity) (hC₂ h) (by positivity)
      _ = (‖c h‖ ^ (1 / N)) ^ (ω * γ') := by
          rw [← Real.rpow_mul (by positivity)]
          congr 1
          ring
      _ ≤ (q h : ℝ) ^ (ω * γ') := Real.rpow_le_rpow (by positivity) (hAq h) (by positivity)
  have hR4 : (height Q : ℝ) ≤ (q 0 : ℝ) ^ (ω * γ' * d 0) := by
    calc (height Q : ℝ) ≤ height P := by exact_mod_cast hQH
      _ ≤ ‖c 0‖ ^ (ω * γ * d 0 / N ^ 2) := hheight
      _ = (‖c 0‖ ^ (1 / N)) ^ (ω * γ' * d 0) := by
          rw [← Real.rpow_mul (by positivity)]
          congr 1
          rw [hγ']
          field_simp
      _ ≤ (q 0 : ℝ) ^ (ω * γ' * d 0) := Real.rpow_le_rpow (by positivity) (hAq 0) (by positivity)
  obtain ⟨j, hjw, hjne⟩ := roth_lemma m ε hε0 hε1 d hd hR1 γ' hγ'0 hγ'1 p q hq hpq hR2 hR3 Q
    hQ0 hQdeg hR4
  have hpt : (fun h ↦ (p h : ℚ) / q h) = fun h ↦ -(c h (k₂ h) : ℚ) / c h (k₁ h) :=
    funext hpqα
  rw [hpt] at hjne
  obtain ⟨x, hx, i, hi, hine⟩ := hQred j hjne
  exact ⟨x, hx, i, by rw [hi]; linarith, hine⟩

end Schmidt
