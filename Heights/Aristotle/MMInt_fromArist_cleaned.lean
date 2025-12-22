/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 516dc9fe-2721-49bd-9fce-3feb2b34f822

The following was proved by Aristotle:

- lemma miao (hlc : ‖(map (Int.castRingHom ℂ) p).leadingCoeff‖ = 1) (hpx : ¬ X ∣ p)
    (hroots : (Multiset.map (fun a ↦ max 1 ‖a‖) (map (Int.castRingHom ℂ) p).roots).prod = 1)
    {z : ℂ} (hz : z ∈ p.aroots ℂ) :
    ∃ n, 0 < n ∧ z ^ n = 1
-/

import Mathlib


namespace Polynomial

variable {p : ℤ[X]}

noncomputable section AristotleLemmas

lemma aaa {α : Type u_1} {β : Type u_2} [CommMonoid α] [CommMonoidWithZero β] [PartialOrder β] [PosMulMono β] [ZeroLEOneClass β]
    (f : α → β) (h1 : ∀ (a : α), 1 ≤ f a) (s : Multiset α) (a : α) (ha : a ∈ s) :
    f a ≤ (Multiset.map f s).prod := by
  obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [Multiset.map_cons, Multiset.prod_cons]
  calc f a = f a * 1 := (mul_one (f a)).symm
    _ ≤ f a * (Multiset.map f s').prod := by
      gcongr
      · exact le_trans (zero_le_one' β) <| MulOpposite.one_le_op.mp (h1 a)
      · refine Multiset.one_le_prod ?_
        simp_all


/-
If the product of max(1, |root|) for all roots is 1, then every root has absolute value at most 1.
-/
lemma roots_le_one {p : ℤ[X]} (hroots :
    (Multiset.map (fun a ↦ max 1 ‖a‖) (Polynomial.map (Int.castRingHom ℂ) p).roots).prod = 1)
    (z : ℂ) (hz : z ∈ (Polynomial.map (Int.castRingHom ℂ) p).roots) : ‖z‖ ≤ 1 := by
  contrapose! hroots
  apply ne_of_gt <| lt_of_lt_of_le (lt_sup_of_lt_right (a := 1) hroots) _
  exact aaa (fun a => max 1 ‖a‖) (fun a => by aesop) (Polynomial.map (Int.castRingHom ℂ) p).roots z hz

/-
If the product of max(1, |root|) is 1, the leading coefficient is 1, and 0 is not a root, then every root has absolute value 1.
-/
lemma roots_norm_eq_one {p : ℤ[X]} (hlc : ‖(Polynomial.map (Int.castRingHom ℂ) p).leadingCoeff‖ = 1)
    (hpx : ¬ Polynomial.X ∣ p)
    (hroots : (Multiset.map (fun a ↦ max 1 ‖a‖) (Polynomial.map (Int.castRingHom ℂ) p).roots).prod = 1)
    (z : ℂ) (hz : z ∈ (Polynomial.map (Int.castRingHom ℂ) p).roots) : ‖z‖ = 1 := by
  -- By Lemma 2, every root has absolute value at most 1.
  have h_le_one : ∀ z : ℂ, z ∈ (Polynomial.map (Int.castRingHom ℂ) p).roots → ‖z‖ ≤ 1 := by
    convert roots_le_one hroots using 1;
  -- By Lemma 3, since the product of the roots is $\pm p(0)$ and $|p(0)| \ge 1$, the product of the norms of the roots is also $\ge 1$.
  have h_prod_ge_one : ∏ z ∈ (Polynomial.map (Int.castRingHom ℂ) p).roots.toFinset, ‖z‖ ^ (Polynomial.rootMultiplicity z (Polynomial.map (Int.castRingHom ℂ) p)) ≥ 1 := by
    -- Since the product of the roots is $\pm p(0)$ and $|p(0)| \ge 1$, the product of the norms of the roots is also $\ge 1$.
    have h_prod_ge_one : ‖(Polynomial.map (Int.castRingHom ℂ) p).eval 0‖ ≥ 1 := by
      norm_num [ Polynomial.eval_map ] at * ; aesop;
      exact mod_cast abs_pos.mpr <| show p.coeff 0 ≠ 0 from fun h => hpx <| by simpa [ h ] using Polynomial.X_dvd_iff.mpr <| by aesop;
    have h_prod_roots : Polynomial.map (Int.castRingHom ℂ) p = Polynomial.C (Polynomial.leadingCoeff (Polynomial.map (Int.castRingHom ℂ) p)) * ∏ z ∈ (Polynomial.map (Int.castRingHom ℂ) p).roots.toFinset, (Polynomial.X - Polynomial.C z) ^ (Polynomial.rootMultiplicity z (Polynomial.map (Int.castRingHom ℂ) p)) := by
      convert Polynomial.eq_prod_roots_of_splits_id _;
      · norm_num [ Finset.prod_multiset_map_count ];
      · sorry
        --refine Or.inr ?_;
        --intro g hg hdvd; have := Polynomial.degree_eq_one_of_irreducible_of_root hg ( show Polynomial.IsRoot g ↑ ( Classical.choose ( Complex.exists_root <| Polynomial.degree_pos_of_irreducible hg ) ) from Classical.choose_spec ( Complex.exists_root <| Polynomial.degree_pos_of_irreducible hg ) ) ; aesop;
      · sorry
    replace h_prod_roots := congr_arg ( Polynomial.eval 0 ) h_prod_roots ; simp_all +decide [ Polynomial.eval_prod ] ;
  contrapose h_prod_ge_one;
  rw [ Finset.prod_eq_prod_diff_singleton_mul <| show z ∈ ( Polynomial.map ( Int.castRingHom ℂ ) p |> Polynomial.roots |> Multiset.toFinset ) from by aesop ];
  refine' not_le.mpr ( lt_of_le_of_lt ( mul_le_of_le_one_left ( by positivity ) ( Finset.prod_le_one ( fun _ _ => by positivity ) fun x hx => pow_le_one₀ ( by positivity ) ( h_le_one x ( by aesop ) ) ) ) ( pow_lt_one₀ ( by positivity ) ( lt_of_le_of_ne ( h_le_one z hz ) h_prod_ge_one ) ( by aesop ) ) )

/-
If a complex number is an algebraic integer and all its conjugates have absolute value 1, then it is a root of unity.
-/
open IntermediateField in
lemma complex_pow_eq_one_of_isIntegral_of_norm_eq_one {x : ℂ} (h_alg_int : IsIntegral ℤ x)
    (h_conj : ∀ w : ℂ, (minpoly ℤ x).aeval w = 0 → ‖w‖ = 1) :
    ∃ n, 0 < n ∧ x ^ n = 1 := by
  -- Apply the theorem `NumberField.Embeddings.pow_eq_one_of_norm_eq_one` to conclude that $x$ is a root of unity.
  let y : adjoin ℚ {x} := ⟨x, mem_adjoin_simple_self ℚ x⟩
  letI : NumberField (adjoin ℚ {x}) := by
    refine { to_charZero := IntermediateField.charZero ℚ⟮x⟯,
             to_finiteDimensional := adjoin.finiteDimensional h_alg_int.tower_top }
  letI : Nonempty (adjoin ℚ {x} →+* ℂ) := by
    apply NumberField.Embeddings.instNonemptyRingHom ↥ℚ⟮x⟯ ℂ

  have h_values (φ : (adjoin ℚ {x}) →+* ℂ) : ‖φ y‖ = 1 := by
    have h_poly : aeval y (minpoly ℤ x) = 0 := by
        convert minpoly.aeval ℤ x
        simp [aeval_def, eval₂_eq_sum_range, ← Subtype.coe_inj, y]
    apply h_conj
    simpa [aeval_def] using congr_arg φ h_poly
  suffices ∃ n : ℕ, (0 < n ∧ y ^ n = 1) by simp_all [y, Subtype.ext_iff]
  -- By `NumberField.Embeddings.pow_eq_one_of_norm_eq_one`, $x$ is a root of unity.
  convert NumberField.Embeddings.pow_eq_one_of_norm_eq_one (x := y) (adjoin ℚ {x}) ℂ
  · simp_all only [exists_prop, forall_const, Classical.imp_iff_left_iff, y]
    obtain ⟨p, hp⟩ := h_alg_int;
    rw [algebraMap_int_eq] at hp;
    refine Or.inl ⟨p, hp.1, ?_⟩;
    simp_all only [algebraMap_int_eq, eval₂_eq_sum_range, eq_intCast, SubmonoidClass.mk_pow,
      ← Subtype.coe_inj, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul,
      SubringClass.coe_intCast, ZeroMemClass.coe_zero]

end AristotleLemmas

set_option maxHeartbeats 500000 in
lemma miao (hlc : ‖(map (Int.castRingHom ℂ) p).leadingCoeff‖ = 1) (hpx : ¬ X ∣ p)
    (hroots : (Multiset.map (fun a ↦ max 1 ‖a‖) (map (Int.castRingHom ℂ) p).roots).prod = 1)
    {z : ℂ} (hz : z ∈ p.aroots ℂ) :
    ∃ n, 0 < n ∧ z ^ n = 1 := by
  -- By `roots_norm_eq_one`, every root of $p$ has absolute value 1.
  have h_abs_one : ∀ z ∈ (Polynomial.map (Int.castRingHom ℂ) p).roots, ‖z‖ = 1 := by
    apply roots_norm_eq_one hlc hpx hroots;
  -- Since $p$ is monic up to sign, $z$ is an algebraic integer.
  have h_alg_int : IsIntegral ℤ z := by
    -- Since $p$ is monic up to sign, $z$ is a root of a monic polynomial with integer coefficients.
    have h_monic : ∃ q : Polynomial ℤ, q.Monic ∧ q.map (Int.castRingHom ℂ) = Polynomial.map (Int.castRingHom ℂ) p ∨ q.Monic ∧ q.map (Int.castRingHom ℂ) = -Polynomial.map (Int.castRingHom ℂ) p := by
      use if p.leadingCoeff = 1 then p else if p.leadingCoeff = -1 then -p else 1; aesop;
      · exact Or.inl h;
      · simp_all ( config := { decide := Bool.true } ) [ Polynomial.Monic ];
      · erw [ Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero ] at hlc <;> aesop;
        norm_cast at hlc; rw [ abs_eq ] at hlc <;> aesop;
    aesop;
    · refine' ⟨ w, left_1, _ ⟩;
      simp_all +decide [ Polynomial.eval₂_eq_eval_map ];
    · refine' ⟨ w, left_1, _ ⟩ ; replace right_1 := congr_arg ( Polynomial.eval z ) right_1 ; aesop;
      rwa [ Polynomial.eval_map ] at right_1;
  -- The conjugates of $z$ are roots of the minimal polynomial of $z$, which divides $p$. Therefore, every conjugate of $z$ is also a root of $p$.
  have h_conj : ∀ w : ℂ, (Polynomial.map (Int.castRingHom ℂ) (minpoly ℤ z)).eval w = 0 → w ∈ (Polynomial.map (Int.castRingHom ℂ) p).roots := by
    -- Since the minimal polynomial of $z$ divides $p$, any root of the minimal polynomial is also a root of $p$.
    have h_min_div_p : (minpoly ℤ z) ∣ p := by
      refine' minpoly.isIntegrallyClosed_dvd h_alg_int _ ; aesop;
      rwa [ Polynomial.eval_map ] at right;
    cases h_min_div_p ; aesop;
  apply_rules [ complex_pow_eq_one_of_isIntegral_of_norm_eq_one ];
  bound;
  exact h_abs_one w ( h_conj w <| by simpa [ Polynomial.eval_map ] using a )

end Polynomial
