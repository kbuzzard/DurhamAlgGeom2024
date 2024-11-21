import Mathlib
set_option linter.style.header false

/-

Let `S` be an ℕ-graded ring. Recall that in Lean an ℕ-grading
is represented by `𝒜 : ℕ → Submodule R₀ S` where `R₀` is some
auxiliary base ring (for example you could imagine `R₀ = ℤ`).

Recall that if `f` is a homogeneous element (e.g. `f ∈ 𝒜 d` for
some natural `d`) then we can form the so-called "homogeneous localization"
of `S` at `f`, written `S_{(f)}` in LaTeX and
written `HomogeneousLocalization.Away 𝒜 f` in Lean,
or just `Away 𝒜 f` if we have `open`ed `HomogeneousLocalization`).
This ring is the subring of the `ℤ`-graded ring `S[1/f]` consisting
of degree `0` elements.

In this file we show two things.

1) If `f,g` are homogeneous elements of `S`, then there's a natural map
from `S_{(f)}` to `S_{(fg)}`, sending `x/f^n` to `xg^n/(fg)^n` if `x`
is homogeneous of degree `n*deg(f)`. We show this by first constructing
the canonical map `S[1/f] → S[1/fg]` and then showing that it sends the
subring `S_{(f)}` to `S_{(fg)}`. Our proof is slightly complicated by
the fact that `S_{(f)}` is not actually *defined* as a subring of `S[1/f]` in Lean,
but there is an injective map between the two rings so it's OK.

2) From (1) we can deduce that there's a bilinear map `S_{(f)} × S_{(g)} → S_{(fg)}`
and hence a map `S_{(f)} ⊗[ℤ] S_{(g)} → S_{(fg)}`. We prove that this map
is surjective.
-/

section ring_theory_lifting
-- let A,B,C be commutative rings
variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
-- Say we have ring homs `φ : A → C` and `ψ : B → C`, with the following two
-- properties:
-- (i) im(φ) ⊆ im(ψ)
-- (ii) ψ is injective
-- Then there's a ring hom α : A → B making the triangle commute.
-- Proof: if a ∈ A then φ(a) ∈ C is in the image of ψ by assumption (i)
-- so lifts to B, and by (ii) the lift is unique.

variable {φ : A →+* C} {ψ : B →+* C} (hi : Set.range φ ⊆ Set.range ψ)
  (hii : Function.Injective ψ)

/-- A "random" lift `A → B` of `φ` along `ψ`, using hypothesis (i). Just
a function, not a ring homomorphism. See `lift_of_range_sub_range_of_injective`
for the ring homomorphism. -/
private noncomputable def lift_aux : A → B :=
  fun a ↦ (hi ⟨a, rfl⟩).choose -- uses the axiom of choice in Lean's type theory
-- The fact that `lift_aux` is a lift
@[simp]
lemma lift_aux_spec (a : A) : ψ (lift_aux hi a) = φ a :=
  (hi ⟨a, rfl⟩).choose_spec

include hii in
/-- The ring homomorphism lifting `φ` along an injective map `ψ` under
the assumption that im(φ) ⊆ im(ψ). -/
noncomputable def lift_of_range_sub_range_of_injective : A →+* B where
  toFun := lift_aux hi
  map_one' := by
    apply hii
    simp
  map_mul' x y := by
    apply hii
    simp only [lift_aux_spec, map_mul]
  map_zero' := by
    apply hii
    simp
  map_add' x y := by
    apply hii
    simp

end ring_theory_lifting

noncomputable section part1
-- missing API for `Localization.awayLift`
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
-- Say d and e are naturals
variable {d e : ℕ}
-- Apparently we don't need that d,e are positive here?
-- [NeZero d] [NeZero e]
-- Say f and g are homogeneous of degrees d and e
variable {f : S} (hf : f ∈ 𝒜 d)
variable {g : S} (hg : g ∈ 𝒜 e)
-- let's not have to type HomogeneousLocalization everywhere
open HomogeneousLocalization
open Submonoid (powers)
-- Let's define a map from S_(f) to S_(fg)
variable {x : S} (hx : x = f * g)

include hx

lemma lemma1' : ((algebraMap S (Localization.Away x)) f)*(Localization.mk g (by exact ⟨f*g, 1, by simp [hx]⟩)) = 1 := by
  rw [←Algebra.smul_def, Localization.smul_mk]
  exact Localization.mk_self ⟨f*g, _⟩

lemma lemma1 : IsUnit ((algebraMap S (Localization.Away x)) f) := by
  rw [isUnit_iff_exists_inv]
  exact ⟨_, lemma1' hx⟩
/-

         what we want
S_{(f)} -----------------> S_{(fg)}
 |                             |
 | val                         | val
 |                             |
 \/    universal property      \/
S[1/f] -----------------> S[1/(fg)]
-/
-- map1 is the diagonal map; we will later on lift it to get what we want
def map1 : Away 𝒜 f →+* Localization.Away x :=
  (Localization.awayLift (algebraMap S _) _ (lemma1 hx)).comp
    (algebraMap (Away 𝒜 f) (Localization.Away f))

-- this could be golfed/tidied
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
    rw [←Algebra.smul_def, Localization.mk_pow, Localization.smul_mk]
    simp_rw [hx]
    rfl
  · apply SetLike.mul_mem_graded ha
    convert SetLike.pow_mem_graded _ hg
  · rw [hx, mul_pow]
    apply SetLike.mul_mem_graded hb'
    convert SetLike.pow_mem_graded _ hg

/-- The map needed for part (1) of the theorem. -/
def map2 : Away 𝒜 f →+* Away 𝒜 x :=
  lift_of_range_sub_range_of_injective (φ := map1 𝒜 hx)
  (ψ := algebraMap (Away 𝒜 x) (Localization.Away x))
  (lemma2 𝒜 hg hx) (val_injective _)
-- the defining property of map2
lemma map2_spec :
    (algebraMap (Away 𝒜 x) (Localization.Away x)).comp (map2 𝒜 hg hx) = map1 𝒜 hx := by
  ext a
  dsimp
  have foo : Set.range ⇑(map1 𝒜 hx) ⊆ Set.range ⇑(algebraMap (Away 𝒜 x) (Localization.Away x)) :=
    lemma2 𝒜 hg hx
  exact lift_aux_spec foo a
@[simp]
lemma map2_spec' (z) :
    (map2 𝒜 hg hx z).val = map1 𝒜 hx z := by
  have foo : Set.range ⇑(map1 𝒜 hx) ⊆ Set.range ⇑(algebraMap (Away 𝒜 x) (Localization.Away x)) :=
    lemma2 𝒜 hg hx
  exact lift_aux_spec foo z

lemma map2_spec_mk (z) :
    (map2 𝒜 hg hx z).val = map1 𝒜 hx z := by
  have foo : Set.range ⇑(map1 𝒜 hx) ⊆ Set.range ⇑(algebraMap (Away 𝒜 x) (Localization.Away x)) :=
    lemma2 𝒜 hg hx
  exact lift_aux_spec foo z

lemma val_map2_mk (n a i hi) : (map2 𝒜 hg hx (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩)).val =
    Localization.mk (a * g ^ i) ⟨x ^ i, (Submonoid.mem_powers_iff _ _).mpr ⟨i, rfl⟩⟩ := by
  rw [map2_spec_mk]
  simp [map1]
  rw [Localization.awayLift_mk (hv := lemma1' hx), ← Localization.mk_one_eq_algebraMap,
    Localization.mk_pow, Localization.mk_mul]
  simp [hx]
  congr

lemma map2_fromZeroRingHom (a) :
    map2 𝒜 hg hx (fromZeroRingHom 𝒜 _ a) = fromZeroRingHom 𝒜 _ a := by
  ext
  convert val_map2_mk 𝒜 hg hx 0 a 0 (by simpa using SetLike.GradedOne.one_mem) <;>
    simp [fromZeroRingHom]; rfl

/-

## We now prove part (2)
-/

omit hx -- no longer needed

open scoped TensorProduct

def tensormap : Away 𝒜 f ⊗[ℤ] Away 𝒜 g →+* Away 𝒜 (f * g) :=
  (Algebra.TensorProduct.lift
    (RingHom.toIntAlgHom <| map2 𝒜 hg rfl)
    (RingHom.toIntAlgHom <| map2 𝒜 hf <| mul_comm f g)
    (by intros; apply Commute.all)).toRingHom
-- part (2)
lemma tensormap_surjective (hd:d ≠0) : Function.Surjective (tensormap 𝒜 hf hg) := by
  unfold Function.Surjective
  intro z
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb'⟩, ⟨j, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective z
  dsimp at hb'
  dsimp
  by_cases hfg:(f * g) ^ j = 0
  · use 0
    have := HomogeneousLocalization.subsingleton 𝒜 (x:= Submonoid.powers (f*g)) (by
      rw [← hfg]
      use j)
    apply this.elim
  have : n = j*(d+e) := by
    apply DirectSum.degree_eq_of_mem_mem 𝒜 hb'
    convert SetLike.pow_mem_graded _ _ using 2
    infer_instance
    exact SetLike.mul_mem_graded hf hg
    exact hfg
  let x0 : NumDenSameDeg 𝒜 (.powers f) := {
    deg := j*(d*(e+1))
    num := ⟨a*g^(j*(d-1)), by
      convert SetLike.mul_mem_graded ha ( SetLike.pow_mem_graded _ hg) using 2
      rw [this]
      cases d
      contradiction
      simp only [add_tsub_cancel_right, smul_eq_mul]
      ring⟩
    den := ⟨f^(j*(e+1)), by
      convert SetLike.pow_mem_graded _ hf using 2
      ring⟩
    den_mem := ⟨_,rfl⟩
  }
  let y0 : NumDenSameDeg 𝒜 (.powers g) := {
    deg := j*(d*e)
    num := ⟨f^(j*e),by
      convert SetLike.pow_mem_graded _ hf using 2
      ring⟩
    den := ⟨g^(j*d),by
      convert SetLike.pow_mem_graded _ hg using 2
      ring⟩
    den_mem := ⟨_,rfl⟩
  }
  use (mk x0 ⊗ₜ[ℤ] mk y0)
  simp only [tensormap]
  ext
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
    RingHom.toIntAlgHom_coe, val_mul, map2_spec', map1, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, val_mk]
  rw [Localization.awayLift_mk (hv:=lemma1' rfl),
    Localization.awayLift_mk (hv:=lemma1' (mul_comm _ _))]
  simp only [Localization.mk_mul, ← Localization.mk_one_eq_algebraMap, Localization.mk_pow]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  dsimp
  use 1
  simp only [OneMemClass.coe_one, one_mul]
  cases d
  contradiction
  simp only [add_tsub_cancel_right]
  ring
