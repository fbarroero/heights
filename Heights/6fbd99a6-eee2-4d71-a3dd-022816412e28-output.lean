/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6fbd99a6-eee2-4d71-a3dd-022816412e28

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem foo (s : Finset ℚ) : s.lcmDen ℤ = s.lcm (fun x ↦ (x.den : ℤ))

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib



variable {R K : Type*} [DecidableEq R] [CommSemiring R] [CancelCommMonoidWithZero R]
[NormalizedGCDMonoid R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

namespace Finset

variable (s : Finset K)

variable (R) in
noncomputable def lcmDen : R := s.lcm (fun x ↦
  let q := (IsLocalization.sec (nonZeroDivisors R) x)
  normalize <| Classical.choose (GCDMonoid.gcd_dvd_right q.1 q.2))

--#eval ((singleton 1 : Finset ℚ)).lcmDen ℤ

theorem aa (x : ℤ) : normalize x = x.natAbs := by
  simp [normalize, normUnit, abs]
  by_cases h : 0 ≤ x
  simp [h]
  simp [h]
  omega

noncomputable section AristotleLemmas

/-
If `n/d = x` in rationals, then `d / gcd(n, d)` (in absolute value) is equal to the denominator of `x`.
-/
theorem int_div_gcd_eq_den (n d : ℤ) (x : ℚ) (hd : d ≠ 0) (h : (n : ℚ) = d * x) :
  (d / (Int.gcd n d : ℤ)).natAbs = x.den := by
    -- By definition of gcd, we know that there exist integers $k$ and $m$ such that $n = kg$ and $d = mg$, where $g = \gcd(n, d)$.
    set g := Int.gcd n d with hg
    obtain ⟨k, hk⟩ : ∃ k : ℤ, n = g * k := by
      exact Int.gcd_dvd_left n d
    obtain ⟨m, hm⟩ : ∃ m : ℤ, d = g * m := by
      exact Int.gcd_dvd_right n d
    have h_coprime : Int.gcd k m = 1 := by
      rw [ hk, hm, Int.gcd_mul_left ] at hg;
      nlinarith [ abs_of_nonneg ( by positivity : ( 0 : ℤ ) ≤ g ), show g > 0 from Int.gcd_pos_of_ne_zero_right _ hd ];
    -- From $g * k = (g * m) * x$, we get $k = m * x$. Since $x$ is rational, $k$ and $m$ are integers.
    have h_eq : k = m * x := by
      exact mul_left_cancel₀ ( show ( g : ℚ ) ≠ 0 by norm_cast; exact mt Int.gcd_eq_zero_iff.mp ( by intro t; simp_all +singlePass ) ) ( by push_cast [ hk, hm ] at h ⊢; linarith );
    -- Since $k$ and $m$ are coprime, $x = k / m$ is in lowest terms.
    have h_lowest_terms : x = k / m := by
      rw [ h_eq, mul_div_cancel_left₀ _ ( by rintro h; simp_all +singlePass ) ]
    have h_den : x.den = m.natAbs := by
      rw [ h_lowest_terms, div_eq_mul_inv ] ; simp +decide [ Rat.mul_den, h_coprime ] ;
      cases eq_or_ne m 0 <;> simp +decide [ Int.natAbs_mul, Int.natAbs_sign, ‹_› ] at *;
      · contradiction;
      · rw [ Int.gcd_eq_natAbs ] at h_coprime ; simp +decide [ h_coprime ]
    rw [hm] at *; simp [h_den];
    rw [ Int.mul_ediv_cancel_left _ ( Nat.cast_ne_zero.mpr <| mt Int.gcd_eq_zero_iff.mp <| by simp +decide [ hd ] ) ]

end AristotleLemmas

theorem foo (s : Finset ℚ) : s.lcmDen ℤ = s.lcm (fun x ↦ (x.den : ℤ)) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [lcmDen]
  | insert a s has hind =>
    --simp [lcmDen]
    simp [← hind, lcmDen]
    /- apply lcm_eq_of_associated_left
    rw [@Int.associated_iff]
 -/
    -- Apply the lemma that states the denominator of a rational number is equal to the absolute value of the denominator of its numerator divided by the gcd of the numerator and denominator.
    have h_denom : ∀ (n d : ℤ) (x : ℚ), d ≠ 0 → (n : ℚ) = d * x → (d / (Int.gcd n d : ℤ)).natAbs = x.den := by
      exact fun n d x a a_1 ↦ int_div_gcd_eq_den n d x a a_1
    --generalize_proofs at *;
    -- Apply the lemma `h_denom` to conclude that the denominator of `a` is equal to the absolute value of the denominator of its numerator divided by the gcd of the numerator and denominator.
    have h_denom_eq : (Int.natAbs (Classical.choose (GCDMonoid.gcd_dvd_right (IsLocalization.sec (nonZeroDivisors ℤ) a).1 (IsLocalization.sec (nonZeroDivisors ℤ) a).2))) = a.den := by
      convert h_denom ( IsLocalization.sec ( nonZeroDivisors ℤ ) a |>.1 ) ( IsLocalization.sec ( nonZeroDivisors ℤ ) a |>.2 ) a _ _ using 1
      all_goals generalize_proofs at *;
      · rw [ Int.ediv_eq_of_eq_mul_left ] <;> norm_cast
        all_goals generalize_proofs at *;
        · exact Nat.ne_of_gt ( Int.gcd_pos_of_ne_zero_right _ <| by simp );
        · convert Classical.choose_spec ‹∃ x : ℤ, ( IsLocalization.sec ( nonZeroDivisors ℤ ) a |>.2 : ℤ ) = GCDMonoid.gcd ( IsLocalization.sec ( nonZeroDivisors ℤ ) a |>.1 ) ( IsLocalization.sec ( nonZeroDivisors ℤ ) a |>.2 : ℤ ) * x› using 1 ; ring!;
      · exact IsLocalization.sec_snd_ne_zero (fun ⦃x⦄ a ↦ a) a;
      · convert IsLocalization.sec_spec ( nonZeroDivisors ℤ ) a |> Eq.symm using 1 ; ring!;
    simp +decide [ ← h_denom_eq, normalize_apply ];
    simp +decide [ NormalizationMonoid.normUnit ]
    generalize_proofs at *;
    split_ifs <;> simp +decide [ *, abs_of_nonneg, abs_of_nonpos ];
    rw [ abs_of_nonpos ( le_of_not_ge ‹_› ) ]

/-
  suffices (s.lcmDen ℤ).natAbs = (s.lcm (fun x ↦ (x.den : ℤ))).natAbs by
    convert this
    refine Iff.symm (Int.natAbs_inj_of_nonneg_of_nonneg ?_ ?_)
    simp [lcmDen, lcm_eq_normalize]

    sorry
    sorry
  apply Nat.dvd_antisymm
  sorry -/
  /- simp [lcmDen, Finset.lcm_def, lcm]


  congr
  ext x -/

  --sorry


end Finset
