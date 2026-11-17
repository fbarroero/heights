module

public import Mathlib

/-!
# A reduction lemma for bases

This file contains [evertse1993], Lemma 3.3.5, which replaces Davenport's lemma and Mahler's
results on compound convex bodies in Schmidt's original proof of the Subspace Theorem.

Let `l₁, …, lₙ` be linearly independent linear forms on a real vector space with basis
`b₁, …, bₙ` such that `|lᵢ(bⱼ)| ≤ μⱼ` for all `i`, `j`, where `μ₁ ≤ ⋯ ≤ μₙ`. Then there are a
permutation `κ` and vectors `vⱼ = bⱼ + ξⱼ₁ b₁ + ⋯ + ξⱼ,ⱼ₋₁ bⱼ₋₁` with `ξⱼₖ ∈ ℤ` such that
`|l_{κ(i)}(vⱼ)| ≤ 2 ^ (i + j) μ_{min(i, j)}` for all `i`, `j`.

We state this in terms of the matrix `M = (lᵢ(bⱼ))`: the matrix `(lᵢ(vⱼ))` is then `M * U`, where
`U` is an upper triangular matrix with integer entries and with ones on the diagonal.
-/

@[expose] public section

open Matrix

namespace Schmidt

/-- `1 + 2 + ⋯ + 2 ^ (n - 1) ≤ 2 ^ n`. -/
private lemma sum_two_pow_le (n : ℕ) : ∑ i : Fin n, (2 : ℝ) ^ (i : ℕ) ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [pow_succ]
    linarith

/-- Given an invertible `(n + 1) × (n + 1)` matrix `M`, there is a row `p` which, on the first `n`
columns, is a linear combination with coefficients of absolute value `≤ 1` of the other rows, and
such that deleting the row `p` and the last column gives an invertible matrix. -/
private lemma exists_pivot {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hM : M.det ≠ 0) :
    ∃ (p : Fin (n + 1)) (β : Fin n → ℝ), (∀ i, |β i| ≤ 1) ∧
      (∀ j : Fin n, M p j.castSucc = ∑ i, β i * M (p.succAbove i) j.castSucc) ∧
      (M.submatrix p.succAbove Fin.castSucc).det ≠ 0 := by
  classical
  -- a nonzero vector in the left kernel of the first `n` columns
  have hN : (M.updateCol (Fin.last n) 0).det = 0 :=
    Matrix.det_eq_zero_of_column_eq_zero (Fin.last n) fun i => by simp
  obtain ⟨a, ha0, haN⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hN
  have haj : ∀ j : Fin n, ∑ i, a i * M i j.castSucc = 0 := by
    intro j
    have := congrFun haN j.castSucc
    simpa [Matrix.vecMul, dotProduct, Matrix.updateCol_apply, Fin.castSucc_ne_last] using this
  obtain ⟨p, -, hp⟩ :=
    Finset.exists_max_image Finset.univ (fun i => |a i|) ⟨0, Finset.mem_univ _⟩
  have hap : a p ≠ 0 := by
    intro h0
    apply ha0
    funext i
    have := hp i (Finset.mem_univ _)
    rw [h0, abs_zero] at this
    simpa using abs_nonpos_iff.mp this
  have hrel : ∀ j : Fin n, M p j.castSucc =
      ∑ i, (-a (p.succAbove i) / a p) * M (p.succAbove i) j.castSucc := by
    intro j
    have h1 := haj j
    rw [Fin.sum_univ_succAbove _ p] at h1
    have h2 : ∑ i, (-a (p.succAbove i) / a p) * M (p.succAbove i) j.castSucc =
        (-∑ i, a (p.succAbove i) * M (p.succAbove i) j.castSucc) / a p := by
      rw [← Finset.sum_neg_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, eq_div_iff hap]
    linarith
  refine ⟨p, fun i => -a (p.succAbove i) / a p, fun i => ?_, hrel, ?_⟩
  · rw [abs_div, abs_neg]
    exact div_le_one_of_le₀ (hp _ (Finset.mem_univ _)) (abs_nonneg _)
  · intro hdet
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    have hcj : ∀ j : Fin n, ∑ i, c i * M (p.succAbove i) j.castSucc = 0 := by
      intro j
      have := congrFun hc j
      simpa [Matrix.vecMul, dotProduct] using this
    have hc'j : ∀ j : Fin n, ∑ i, (p.insertNth 0 c : Fin (n + 1) → ℝ) i * M i j.castSucc = 0 := by
      intro j
      rw [Fin.sum_univ_succAbove _ p]
      simp [hcj j]
    have hd : (fun i => (∑ k, (p.insertNth 0 c : Fin (n + 1) → ℝ) k * M k (Fin.last n)) * a i -
        (∑ k, a k * M k (Fin.last n)) * (p.insertNth 0 c : Fin (n + 1) → ℝ) i) ᵥ* M = 0 := by
      funext j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib,
        mul_assoc, ← Finset.mul_sum]
      induction j using Fin.lastCases with
      | last => ring
      | cast j => rw [haj j, hc'j j]; ring
    have hd0 := Matrix.eq_zero_of_vecMul_eq_zero hM hd
    have hrc : ∑ k, (p.insertNth 0 c : Fin (n + 1) → ℝ) k * M k (Fin.last n) = 0 := by
      have := congrFun hd0 p
      simpa [hap] using this
    have hc'M : (p.insertNth 0 c : Fin (n + 1) → ℝ) ᵥ* M = 0 := by
      funext j
      induction j using Fin.lastCases with
      | last => simpa [Matrix.vecMul, dotProduct] using hrc
      | cast j => simpa [Matrix.vecMul, dotProduct] using hc'j j
    have hc'0 := Matrix.eq_zero_of_vecMul_eq_zero hM hc'M
    apply hc0
    funext i
    have := congrFun hc'0 (p.succAbove i)
    simpa using this

/-- Solving a square linear system and rounding the solution to the nearest integers. -/
private lemma exists_round {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
    (c : Fin n → ℝ) :
    ∃ (ξ : Fin n → ℤ) (δ : Fin n → ℝ), (∀ j, |δ j| ≤ 1 / 2) ∧
      ∀ i, c i + ∑ j, A i j * (ξ j : ℝ) = ∑ j, A i j * δ j := by
  have hAt : A *ᵥ (A⁻¹ *ᵥ (-c)) = -c := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA),
      Matrix.one_mulVec]
  generalize A⁻¹ *ᵥ (-c) = t at hAt
  refine ⟨fun j => round (t j), fun j => round (t j) - t j, fun j => ?_, fun i => ?_⟩
  · rw [abs_sub_comm]
    exact abs_sub_round (t j)
  · have h1 := congrFun hAt i
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at h1
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith

/-- Extend a permutation `κ₀` of `Fin n` to a permutation of `Fin (n + 1)` sending the last
element to `p` and `i < n` to `p.succAbove (κ₀ i)`. -/
private lemma exists_perm_extend {n : ℕ} (κ₀ : Equiv.Perm (Fin n)) (p : Fin (n + 1)) :
    ∃ κ : Equiv.Perm (Fin (n + 1)),
      (∀ i, κ i.castSucc = p.succAbove (κ₀ i)) ∧ κ (Fin.last n) = p :=
  ⟨finSuccEquivLast.trans ((Equiv.optionCongr κ₀).trans (finSuccEquiv' p).symm),
    fun i => by simp, by simp⟩

/-- Extend an `n × n` matrix by a last column `w` (with a `1` in the corner) and a last row of
zeros. -/
private lemma exists_matrix_extend {n : ℕ} (U₀ : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℤ) :
    ∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
      (∀ k j : Fin n, U k.castSucc j.castSucc = U₀ k j) ∧
      (∀ j : Fin n, U (Fin.last n) j.castSucc = 0) ∧
      (∀ k : Fin n, U k.castSucc (Fin.last n) = w k) ∧ U (Fin.last n) (Fin.last n) = 1 :=
  ⟨fun k j => Fin.lastCases (motive := fun _ => ℤ)
      (Fin.lastCases (motive := fun _ => ℤ) 1 (fun k' => w k') k)
      (fun j' => Fin.lastCases (motive := fun _ => ℤ) 0 (fun k' => U₀ k' j') k) j,
    fun k j => by simp, fun j => by simp, fun k => by simp, by simp⟩

/-- A version of `exists_unipotent_mul_le` with the bound `μ (min i j)` split into two bounds,
which is more convenient for the induction. -/
private lemma exists_unipotent_mul_le_aux (n : ℕ) :
    ∀ (M : Matrix (Fin n) (Fin n) ℝ), M.det ≠ 0 → ∀ μ : Fin n → ℝ, Monotone μ →
      (∀ i j, |M i j| ≤ μ j) →
      ∃ (κ : Equiv.Perm (Fin n)) (U : Matrix (Fin n) (Fin n) ℤ),
        (∀ j, U j j = 1) ∧ (∀ k j, j < k → U k j = 0) ∧
        ∀ i j, |(M * U.map (Int.cast : ℤ → ℝ)) (κ i) j| ≤ 2 ^ ((i : ℕ) + j + 2) * μ i ∧
          |(M * U.map (Int.cast : ℤ → ℝ)) (κ i) j| ≤ 2 ^ ((i : ℕ) + j + 2) * μ j := by
  induction n with
  | zero =>
    intro M _ μ _ _
    exact ⟨1, 1, fun j => j.elim0, fun k => k.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro M hM μ hμ h
    obtain ⟨p, β, hβ, hrel, hdet⟩ := exists_pivot M hM
    obtain ⟨κ₀, U₀, hU₀d, hU₀t, hb₀⟩ := ih (M.submatrix p.succAbove Fin.castSucc) hdet
      (μ ∘ Fin.castSucc) (hμ.comp Fin.strictMono_castSucc.monotone) (fun i j => h _ _)
    have hAdet : (M.submatrix p.succAbove Fin.castSucc * U₀.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
      have hU : (U₀.map (Int.cast : ℤ → ℝ)).det = 1 := by
        rw [Matrix.det_of_isUpperTriangular]
        · simp [hU₀d]
        · intro i j hij
          simp [hU₀t i j hij]
      rw [Matrix.det_mul, hU, mul_one]
      exact hdet
    generalize hA : M.submatrix p.succAbove Fin.castSucc * U₀.map (Int.cast : ℤ → ℝ) = A
      at hAdet hb₀
    obtain ⟨ξ, δ, hδ, hξ⟩ := exists_round A hAdet (fun i => M (p.succAbove i) (Fin.last n))
    obtain ⟨κ, hκc, hκl⟩ := exists_perm_extend κ₀ p
    obtain ⟨U, hUcc, hUlc, hUcl, hUll⟩ := exists_matrix_extend U₀ (U₀ *ᵥ ξ)
    have hb1 : ∀ i j : Fin n, |A (κ₀ i) j| ≤ 2 ^ ((i : ℕ) + j + 2) * μ i.castSucc :=
      fun i j => (hb₀ i j).1
    have hb2 : ∀ i j : Fin n, |A (κ₀ i) j| ≤ 2 ^ ((i : ℕ) + j + 2) * μ j.castSucc :=
      fun i j => (hb₀ i j).2
    have hξ' : ∀ i, M (p.succAbove i) (Fin.last n) + ∑ j, A i j * (ξ j : ℝ) = ∑ j, A i j * δ j :=
      hξ
    have hδ1 : ∀ j, |δ j| ≤ 1 := fun j => (hδ j).trans (by norm_num)
    have hμ0 : ∀ j, 0 ≤ μ j := fun j => (abs_nonneg _).trans (h 0 j)
    have hμl : ∀ j, μ j ≤ μ (Fin.last n) := fun j => hμ (Fin.le_last j)
    have hG := sum_two_pow_le n
    have hG0 : 0 ≤ ∑ i : Fin n, (2 : ℝ) ^ (i : ℕ) := Finset.sum_nonneg fun i _ => by positivity
    -- the entries of `M * U`
    have hE1 : ∀ i (j : Fin n), (M * U.map (Int.cast : ℤ → ℝ)) i j.castSucc =
        ∑ k : Fin n, M i k.castSucc * (U₀ k j : ℝ) := by
      intro i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      simp [hUcc, hUlc]
    have hE2 : ∀ i, (M * U.map (Int.cast : ℤ → ℝ)) i (Fin.last n) = M i (Fin.last n) +
        ∑ j : Fin n, (∑ k : Fin n, M i k.castSucc * (U₀ k j : ℝ)) * (ξ j : ℝ) := by
      intro i
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      simp only [Matrix.map_apply, hUcl, hUll, Int.cast_one, mul_one, Matrix.mulVec, dotProduct,
        Int.cast_sum, Int.cast_mul]
      rw [add_comm]
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have hA1 : ∀ i j : Fin n,
        ∑ k : Fin n, M (p.succAbove i) k.castSucc * (U₀ k j : ℝ) = A i j := by
      intro i j
      simp [← hA, Matrix.mul_apply]
    have hAp : ∀ j : Fin n, ∑ k : Fin n, M p k.castSucc * (U₀ k j : ℝ) = ∑ i, β i * A i j := by
      intro j
      simp only [← hA1, hrel, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    refine ⟨κ, U, ?_, ?_, ?_⟩
    · intro j
      induction j using Fin.lastCases with
      | last => exact hUll
      | cast j => rw [hUcc]; exact hU₀d j
    · intro k j hjk
      induction k using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hjk (lt_irrefl _)
        | cast j => exact hUlc j
      | cast k =>
        induction j using Fin.lastCases with
        | last => exact absurd hjk (not_lt.mpr (Fin.le_last _))
        | cast j => rw [hUcc]; exact hU₀t k j (Fin.castSucc_lt_castSucc_iff.mp hjk)
    · intro i j
      induction i using Fin.lastCases with
      | cast i =>
        induction j using Fin.lastCases with
        | cast j =>
          rw [hκc, hE1, hA1]
          simp only [Fin.val_castSucc]
          exact ⟨hb1 i j, hb2 i j⟩
        | last =>
          rw [hκc, hE2]
          simp only [hA1, Fin.val_castSucc, Fin.val_last]
          rw [hξ']
          have key : |∑ j, A (κ₀ i) j * δ j| ≤ 2 ^ ((i : ℕ) + n + 2) * μ i.castSucc := by
            calc |∑ j, A (κ₀ i) j * δ j| ≤ ∑ j, |A (κ₀ i) j * δ j| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ j : Fin n, 2 ^ ((i : ℕ) + j + 2) * μ i.castSucc :=
                  Finset.sum_le_sum fun j _ => by
                    rw [abs_mul]
                    exact (mul_le_of_le_one_right (abs_nonneg _) (hδ1 j)).trans (hb1 i j)
              _ = (∑ j : Fin n, (2 : ℝ) ^ (j : ℕ)) * (2 ^ ((i : ℕ) + 2) * μ i.castSucc) := by
                  rw [Finset.sum_mul]
                  exact Finset.sum_congr rfl fun j _ => by ring
              _ ≤ 2 ^ n * (2 ^ ((i : ℕ) + 2) * μ i.castSucc) :=
                  mul_le_mul_of_nonneg_right hG (mul_nonneg (by positivity) (hμ0 _))
              _ = 2 ^ ((i : ℕ) + n + 2) * μ i.castSucc := by ring
          exact ⟨key, key.trans (mul_le_mul_of_nonneg_left (hμl _) (by positivity))⟩
      | last =>
        induction j using Fin.lastCases with
        | cast j =>
          rw [hκl, hE1, hAp]
          simp only [Fin.val_castSucc, Fin.val_last]
          have key : |∑ i, β i * A i j| ≤ 2 ^ (n + (j : ℕ) + 2) * μ j.castSucc := by
            calc |∑ i, β i * A i j| ≤ ∑ i, |β i * A i j| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ i, |A i j| := Finset.sum_le_sum fun i _ => by
                    rw [abs_mul]
                    exact mul_le_of_le_one_left (abs_nonneg _) (hβ i)
              _ = ∑ i, |A (κ₀ i) j| := (Equiv.sum_comp κ₀ (fun i => |A i j|)).symm
              _ ≤ ∑ i : Fin n, 2 ^ ((i : ℕ) + j + 2) * μ j.castSucc :=
                  Finset.sum_le_sum fun i _ => hb2 i j
              _ = (∑ i : Fin n, (2 : ℝ) ^ (i : ℕ)) * (2 ^ ((j : ℕ) + 2) * μ j.castSucc) := by
                  rw [Finset.sum_mul]
                  exact Finset.sum_congr rfl fun i _ => by ring
              _ ≤ 2 ^ n * (2 ^ ((j : ℕ) + 2) * μ j.castSucc) :=
                  mul_le_mul_of_nonneg_right hG (mul_nonneg (by positivity) (hμ0 _))
              _ = 2 ^ (n + (j : ℕ) + 2) * μ j.castSucc := by ring
          exact ⟨key.trans (mul_le_mul_of_nonneg_left (hμl _) (by positivity)), key⟩
        | last =>
          rw [hκl, hE2]
          simp only [hAp, Fin.val_last, and_self]
          have hxi : ∀ i, ∑ j, A i j * (ξ j : ℝ) =
              ∑ j, A i j * δ j - M (p.succAbove i) (Fin.last n) := fun i => by
            linarith [hξ' i]
          have hsw : ∑ j, (∑ i, β i * A i j) * (ξ j : ℝ) =
              ∑ i, β i * (∑ j, A i j * δ j - M (p.succAbove i) (Fin.last n)) := by
            simp only [← hxi, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
          rw [hsw]
          have hS : ∑ i, ∑ j, |A i j| ≤ 2 ^ n * (2 ^ n * (4 * μ (Fin.last n))) := by
            have h4 : 0 ≤ 4 * μ (Fin.last n) := mul_nonneg (by norm_num) (hμ0 _)
            calc ∑ i, ∑ j, |A i j| = ∑ i, ∑ j, |A (κ₀ i) j| :=
                  (Equiv.sum_comp κ₀ (fun i => ∑ j, |A i j|)).symm
              _ ≤ ∑ i : Fin n, ∑ j : Fin n, 2 ^ ((i : ℕ) + j + 2) * μ (Fin.last n) :=
                  Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
                    (hb2 i j).trans (mul_le_mul_of_nonneg_left (hμl _) (by positivity))
              _ = (∑ i : Fin n, (2 : ℝ) ^ (i : ℕ)) *
                    ((∑ j : Fin n, (2 : ℝ) ^ (j : ℕ)) * (4 * μ (Fin.last n))) := by
                  simp only [Finset.sum_mul, Finset.mul_sum]
                  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
              _ ≤ 2 ^ n * (2 ^ n * (4 * μ (Fin.last n))) :=
                  mul_le_mul hG (mul_le_mul_of_nonneg_right hG h4) (mul_nonneg hG0 h4)
                    (by positivity)
          have hT : ∑ i, |β i * (∑ j, A i j * δ j - M (p.succAbove i) (Fin.last n))| ≤
              1 / 2 * ∑ i, ∑ j, |A i j| + n * μ (Fin.last n) := by
            calc ∑ i, |β i * (∑ j, A i j * δ j - M (p.succAbove i) (Fin.last n))|
                ≤ ∑ i : Fin n, (1 / 2 * ∑ j, |A i j| + μ (Fin.last n)) :=
                  Finset.sum_le_sum fun i _ => by
                    rw [abs_mul]
                    refine (mul_le_of_le_one_left (abs_nonneg _) (hβ i)).trans ?_
                    refine (abs_sub _ _).trans (add_le_add ?_ (h _ _))
                    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
                    rw [Finset.mul_sum]
                    refine Finset.sum_le_sum fun j _ => ?_
                    rw [abs_mul, mul_comm]
                    exact mul_le_mul_of_nonneg_right (hδ j) (abs_nonneg _)
              _ = 1 / 2 * ∑ i, ∑ j, |A i j| + n * μ (Fin.last n) := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
                  simp
          have hn1 : (n : ℝ) + 1 ≤ 2 ^ n := by
            have : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
            exact_mod_cast this
          have hx1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
          have h1 : ((n : ℝ) + 1) * μ (Fin.last n) ≤ 2 ^ n * 2 ^ n * μ (Fin.last n) :=
            mul_le_mul_of_nonneg_right
              (hn1.trans (le_mul_of_one_le_right (by positivity) hx1)) (hμ0 _)
          have h2 : 0 ≤ (2 : ℝ) ^ n * 2 ^ n * μ (Fin.last n) :=
            mul_nonneg (by positivity) (hμ0 _)
          have h3 : (2 : ℝ) ^ (n + n + 2) * μ (Fin.last n) =
              4 * (2 ^ n * 2 ^ n * μ (Fin.last n)) := by
            ring
          rw [h3]
          refine (abs_add_le _ _).trans ?_
          have h5 := (Finset.abs_sum_le_sum_abs
            (fun i => β i * (∑ j, A i j * δ j - M (p.succAbove i) (Fin.last n)))
            Finset.univ).trans hT
          have h6 := h p (Fin.last n)
          linarith

/-- [evertse1993], Lemma 3.3.5. Let `M` be an invertible real `n × n` matrix whose `j`-th column
is bounded by `μⱼ`, where `μ₀ ≤ ⋯ ≤ μₙ₋₁`. Then there are a permutation `κ` and an upper
triangular integer matrix `U` with ones on the diagonal such that the entry `(κ i, j)` of `M * U`
is bounded by `2 ^ (i + j + 2) * μ_{min(i, j)}`. (The indices start from `0`, which explains the
shift in the exponent.) -/
theorem exists_unipotent_mul_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.det ≠ 0)
    (μ : Fin n → ℝ) (hμ : Monotone μ) (h : ∀ i j, |M i j| ≤ μ j) :
    ∃ (κ : Equiv.Perm (Fin n)) (U : Matrix (Fin n) (Fin n) ℤ),
      (∀ j, U j j = 1) ∧ (∀ k j, j < k → U k j = 0) ∧
      ∀ i j, |(M * U.map (Int.cast : ℤ → ℝ)) (κ i) j| ≤ 2 ^ ((i : ℕ) + j + 2) * μ (min i j) := by
  obtain ⟨κ, U, hd, ht, hb⟩ := exists_unipotent_mul_le_aux n M hM μ hμ h
  refine ⟨κ, U, hd, ht, fun i j => ?_⟩
  rcases le_total i j with hij | hij
  · rw [min_eq_left hij]
    exact (hb i j).1
  · rw [min_eq_right hij]
    exact (hb i j).2

end Schmidt
