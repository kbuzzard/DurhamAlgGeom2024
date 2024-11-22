import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.AlgebraicGeometry.ValuativeCriterion

import DurhamAlgGeom2024.Tutorial.«06Separated»
open Classical

suppress_compilation

variable {ι R A : Type}
variable [AddCommMonoid ι]
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

open HomogeneousLocalization

variable (f g : A) (d e : ℕ) (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)

instance awayAlgebra : Algebra (Away 𝒜 f) (Away 𝒜 (f * g)) :=
  RingHom.toAlgebra (map2 𝒜 hg rfl)

attribute [local instance] awayAlgebra
omit hf in
lemma algebraMap_eq :
    letI := awayAlgebra 𝒜 f g e hg
    algebraMap (Away 𝒜 f) (Away 𝒜 (f * g)) = map2 𝒜 hg rfl := rfl

-- A_{(fg)} is the localization of A_{(f)} at g^d/f^e
theorem HomogeneousLocalization.Away.isLocalization_mul (hd : d ≠ 0) (he : e ≠ 0):
    letI := awayAlgebra 𝒜 f g e hg
    IsLocalization
      (Submonoid.powers <| mk
        { deg := d * e
          num := ⟨g^d, SetLike.pow_mem_graded d hg⟩
          den := ⟨f^e, by
            convert SetLike.pow_mem_graded e hf using 2
            rw [mul_comm]
            rfl
          ⟩
          den_mem := ⟨_, rfl⟩ } : Submonoid (Away 𝒜 f))
      (Away 𝒜 (f * g)) :=
  letI := awayAlgebra 𝒜 f g e hg
  { map_units' := by
      intro y
      obtain ⟨r,n,rfl⟩ := y
      dsimp
      rw [map_pow, algebraMap_eq]
      apply IsUnit.pow
      rw [isUnit_iff_exists_inv]
      let z : Away 𝒜 (f * g) := mk {
        deg := (d + e)^2
        num := ⟨g^e * f^(2*e+d), by
          have := SetLike.mul_mem_graded (SetLike.pow_mem_graded e hg)
              (SetLike.pow_mem_graded (2 * e + d) hf)
          convert this using 2
          ring
        ⟩
        den := ⟨(f*g) ^ (d + e), by
          have := SetLike.pow_mem_graded (d + e) (SetLike.mul_mem_graded hf hg)
          convert this using 2
          ring
        ⟩
        den_mem := ⟨_, rfl⟩
      }
      use z
      ext
      simp only [val_mul, map2_spec', map1, RingHom.coe_comp, Function.comp_apply,
        HomogeneousLocalization.algebraMap_apply, val_mk, val_one, z]
      let v : Localization.Away (f * g) := Localization.mk g ⟨f * g, Submonoid.mem_powers (f * g)⟩
      rw [Localization.awayLift_mk (v := v)]
      · simp only [map_pow, v]
        rw [←Localization.mk_one_eq_algebraMap]
        simp only [Localization.mk_pow, one_pow, SubmonoidClass.mk_pow, Localization.mk_mul,
          one_mul, Submonoid.mk_mul_mk]
        convert Localization.mk_self _
        ring
      · rw [←Localization.mk_one_eq_algebraMap]
        simp only [Localization.mk_mul, one_mul, v]
        exact Localization.mk_self ⟨f * g, _⟩
    surj' := by
      intro z
      obtain ⟨⟨N, ⟨s, hs⟩, ⟨b, hn⟩, ⟨n, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective z
      dsimp only [smul_eq_mul, id_eq, eq_mpr_eq_cast] at hn ⊢
      by_cases hfg : (f * g) ^ n = 0
      · have : Subsingleton (Away 𝒜 (f * g)) :=
          HomogeneousLocalization.subsingleton _ (by rw [← hfg]; exact ⟨_, rfl⟩)
        use (0, 1)
        exact this.elim _ _
      have N_eq : N = n * (d + e) :=
        DirectSum.degree_eq_of_mem_mem _ hn
          (SetLike.pow_mem_graded n (SetLike.mul_mem_graded hf hg)) hfg
      let x : Away 𝒜 f := mk
        { deg := N + (n*(d - 1))*e
          num :=
            ⟨s * g ^ (n * (d - 1)),
              SetLike.mul_mem_graded hs
                (SetLike.pow_mem_graded _ hg)⟩
          den :=
            ⟨f^(n*(e + 1)), by
              convert SetLike.pow_mem_graded (n * (e + 1)) hf using 2
              rcases d with _|d
              · contradiction
              simp only [add_tsub_cancel_right, smul_eq_mul, N_eq]
              ring⟩
          den_mem := ⟨_, rfl⟩ }
      refine ⟨⟨x, ⟨_, ⟨n, rfl⟩⟩⟩, ?_⟩
      ext
      simp only [algebraMap_eq, map_pow, val_mul, val_mk, val_pow, map2_spec', map1,
        RingHom.coe_comp, Function.comp_apply, HomogeneousLocalization.algebraMap_apply, x]
      let v : Localization.Away (f * g) := Localization.mk g ⟨f * g, Submonoid.mem_powers (f * g)⟩
      have hv : (algebraMap A (Localization.Away (f * g))) f * v = 1 := by
        rw [←Localization.mk_one_eq_algebraMap]
        simp only [Localization.mk_mul, one_mul, v]
        exact Localization.mk_self ⟨f * g, _⟩
      rw [Localization.awayLift_mk (hv := hv), Localization.awayLift_mk (hv := hv)]
      simp only [map_pow, ← Localization.mk_one_eq_algebraMap, Localization.mk_pow, one_pow,
        SubmonoidClass.mk_pow, Localization.mk_mul, one_mul, Submonoid.mk_mul_mk, v]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      use 1
      rcases d with _|d
      · contradiction
      simp only [OneMemClass.coe_one, one_mul, add_tsub_cancel_right]
      ring
    exists_of_eq := by
      intro x y
      obtain ⟨⟨N, ⟨a, ha⟩, ⟨b, hn⟩, ⟨n, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective x
      obtain ⟨⟨M, ⟨b, hb⟩, ⟨b, hm⟩, ⟨m, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective y
      dsimp at hn hm ⊢
      intro H
      rw [algebraMap_eq, HomogeneousLocalization.ext_iff_val] at H
      simp only [map2_spec', map1, RingHom.coe_comp, Function.comp_apply, algebraMap_apply,
        val_mk] at H
      let v : Localization.Away (f * g) := Localization.mk g ⟨f * g, Submonoid.mem_powers (f * g)⟩
      have hv : (algebraMap A (Localization.Away (f * g))) f * v = 1 := by
        rw [←Localization.mk_one_eq_algebraMap]
        simp only [Localization.mk_mul, one_mul, v]
        exact Localization.mk_self ⟨f * g, _⟩
      repeat rw [Localization.awayLift_mk (hv := hv), ←Localization.mk_one_eq_algebraMap] at H
      simp only [Localization.mk_pow, SubmonoidClass.mk_pow, Localization.mk_mul, one_mul, v] at H
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at H
      obtain ⟨⟨ _, ⟨k, rfl⟩⟩, H⟩ := H
      ring_nf at H
      use ⟨_, ⟨k + m + n, rfl⟩⟩
      ext
      simp only [val_mul, val_pow, val_mk, Localization.mk_pow, SubmonoidClass.mk_pow,
        Localization.mk_mul, Submonoid.mk_mul_mk]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      use 1
      simp only [OneMemClass.coe_one, one_mul]
      rcases e with _|e
      · contradiction
      rcases d with _|d
      · contradiction
      ring_nf
      simp only [← pow_add, mul_assoc, ← mul_add] at H ⊢
      rw [show e * (k + m + n) + k + m * 2 + n = (k + m) + (e * (k + m + n) + m + n) by omega,
        show e * (k + m + n) + k + m + n * 2 = (k + m) + (e * (k + m + n) + n * 2) by omega,
        show k + k * d + m + m * d + n + n * d = (k + m + n) + (k * d + m * d + n * d) by omega,
        pow_add, pow_add g,
        show ∀ (a b c d e : A), a * b * (c * d * e) = (a * (c * e)) * (b * d) by intros; ring, H]
      ring }
