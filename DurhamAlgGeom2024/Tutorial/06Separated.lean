import Mathlib
set_option linter.style.header false

noncomputable section statement

lemma Localization.awayLift_mk {R S} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (a : R) (v : S) (hv : f r * v = 1) (j : ℕ) :
    Localization.awayLift f r (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)
      (Localization.mk a ⟨r ^ j, j, rfl⟩) = f a * v ^ j := by
  rw [Localization.mk_eq_mk']
  erw [IsLocalization.lift_mk']
  rw [Units.mul_inv_eq_iff_eq_mul]
  simp [IsUnit.liftRight, mul_assoc, ← mul_pow, (mul_comm _ _).trans hv]


variable {R₀ S : Type}
-- let R₀ and S be commutative rings, and let
-- S be an R₀-algebra
variable [CommRing R₀] [CommRing S] [Algebra R₀ S]
-- Say S is ⨁ 𝒜ᵢ for i ∈ ℕ with the 𝒜ᵢ R₀-submodules
variable (𝒜 : ℕ → Submodule R₀ S) [GradedAlgebra 𝒜]
-- Say d and e are nonzero
variable {d e : ℕ} --[NeZero d] [NeZero e]
-- Say f and g are homogeneous of degrees d and e
variable {f : S} (hf : f ∈ 𝒜 d)
variable {g : S} (hg : g ∈ 𝒜 e)

-- let's not have to type HomogeneousLocalization everywhere
open HomogeneousLocalization
open Submonoid (powers)

-- Let's define a map from S_(f) to S_(fg)
variable {x : S} (hx : x = f * g)

include hx
lemma lemma1 : IsUnit ((algebraMap S (Localization.Away x)) f) := by
  rw [isUnit_iff_exists_inv]
  use Localization.mk g ⟨f*g, 1, by simp [hx]⟩
  rw [←Algebra.smul_def, Localization.smul_mk]
  exact Localization.mk_self ⟨f*g, _⟩

lemma lemma1' : ((algebraMap S (Localization.Away x)) f)*(Localization.mk g (by exact ⟨f*g, 1, by simp [hx]⟩)) = 1 := by
  rw [←Algebra.smul_def, Localization.smul_mk]
  exact Localization.mk_self ⟨f*g, _⟩

def map1 : Away 𝒜 f →+* Localization.Away x :=
  (Localization.awayLift (algebraMap S _) _ (lemma1 hx)).comp
    (algebraMap (Away 𝒜 f) (Localization.Away f))

include hg
lemma lemma2 : Set.range (map1 𝒜 (f := f) hx) ⊆ Set.range (val (𝒜 := 𝒜)) := by
  rw [Set.subset_def]
  intro y
  intro hy
  rw [Set.mem_range] at hy ⊢
  obtain ⟨z, rfl ⟩ := hy
  obtain ⟨⟨ n, ⟨ a, ha⟩ , ⟨b, hb'⟩ , hb⟩ , rfl⟩ := mk_surjective z
  rw [Submonoid.mem_powers_iff] at hb
  obtain ⟨j, rfl⟩ := hb
  use mk ⟨ n+j*e, ⟨ a*g^j, ?_⟩ , ⟨ (x)^j, ?_⟩ , j, rfl⟩

  · simp [map1]
    dsimp at hb
    rw [Localization.awayLift_mk (hv:=lemma1' hx)]
    rw [←Algebra.smul_def, Localization.mk_pow]
    rw [Localization.smul_mk]
    simp_rw [hx]
    rfl
  · apply SetLike.mul_mem_graded ha
    convert SetLike.pow_mem_graded _ hg
  · rw [hx]
    rw [mul_pow]
    apply SetLike.mul_mem_graded hb'
    convert SetLike.pow_mem_graded _ hg
