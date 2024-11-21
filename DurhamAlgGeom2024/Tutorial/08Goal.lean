import DurhamAlgGeom2024.Tutorial.«07Proper»

variable {R₀ S : Type}
variable [CommRing R₀] [CommRing S] [Algebra R₀ S]
variable (𝒜 : ℕ → Submodule R₀ S) [GradedAlgebra 𝒜]

open AlgebraicGeometry CategoryTheory

section

open Proj HomogeneousLocalization

variable {R A : Type}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A)
variable [GradedAlgebra 𝒜]
variable {f}
variable {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
variable {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m') (hm' : 0 < m') {x : A} (hx : x = f * g)

lemma awayToSection_apply (f : A) (x p) :
    (((ProjectiveSpectrum.Proj.awayToSection 𝒜 f).1 x).val p).val =
      IsLocalization.map (M := Submonoid.powers f) (T := p.1.1.toIdeal.primeCompl) _
        (RingHom.id _) (Submonoid.powers_le.mpr p.2) x.val := by
  obtain ⟨x, rfl⟩ := HomogeneousLocalization.mk_surjective x
  show (HomogeneousLocalization.mapId 𝒜 _ _).val = _
  dsimp [HomogeneousLocalization.mapId, HomogeneousLocalization.map]
  rw [Localization.mk_eq_mk', Localization.mk_eq_mk', IsLocalization.map_mk']
  rfl

@[reassoc]
lemma awayMap_awayToSection  :
    CommRingCat.ofHom (map2 𝒜 g_deg hx) ≫ awayToSection 𝒜 x =
      awayToSection 𝒜 f ≫ (Proj 𝒜).presheaf.map (homOfLE (basicOpen_mono _ _ _ ⟨_, hx⟩)).op := by
  ext a
  apply Subtype.ext
  ext ⟨i, hi⟩
  obtain ⟨⟨n, a, ⟨b, hb'⟩, i, rfl : _ = b⟩, rfl⟩ := mk_surjective a
  simp only [CommRingCat.forget_obj, CommRingCat.coe_of, CommRingCat.ofHom, CommRingCat.coe_comp_of,
    RingHom.coe_comp, Function.comp_apply, homOfLE_leOfHom]
  erw [awayToSection_apply]
  rw [val_map2_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    ← Localization.mk_eq_mk']
  refine Localization.mk_eq_mk_iff.mpr ?_
  rw [Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, RingHom.id_apply, one_mul, hx]
  ring

@[reassoc]
lemma basicOpenToSpec_SpecMap_awayMap :
    basicOpenToSpec 𝒜 x ≫ Spec.map (CommRingCat.ofHom (map2 𝒜 g_deg hx)) =
      (Proj 𝒜).homOfLE (basicOpen_mono _ _ _ ⟨_, hx⟩) ≫ basicOpenToSpec 𝒜 f := by
  rw [basicOpenToSpec, Category.assoc, ← Spec.map_comp, awayMap_awayToSection,
    Spec.map_comp, Scheme.Opens.toSpecΓ_SpecMap_map_assoc]
  rfl

@[reassoc]
lemma SpecMap_awayMap_awayι :
    Spec.map (CommRingCat.ofHom (map2 𝒜 g_deg hx)) ≫ awayι 𝒜 f f_deg hm =
      awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m')) := by
  rw [awayι, awayι, Iso.eq_inv_comp, basicOpenIsoSpec_hom, basicOpenToSpec_SpecMap_awayMap_assoc,
  ← basicOpenIsoSpec_hom _ _ f_deg hm, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]

end

lemma Proj.iSup_basicOpen_eq_top' {ι : Type*} (f : ι → S)
    (hfn : ∀ i, ∃ n, f i ∈ 𝒜 n)
    (hf : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) :
    ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤ := by
  classical
  apply Proj.iSup_basicOpen_eq_top
  intro x hx
  convert_to x - GradedRing.projZeroRingHom 𝒜 x ∈ _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have := (eq_iff_iff.mp congr(x ∈ $hf)).mpr trivial
  induction this using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hfn i
    rw [GradedRing.projZeroRingHom_apply]
    by_cases hn' : n = 0
    · rw [DirectSum.decompose_of_mem_same 𝒜 (hn' ▸ hn), sub_self]
      exact zero_mem _
    · rw [DirectSum.decompose_of_mem_ne 𝒜 hn hn', sub_zero]
      exact Ideal.subset_span ⟨_, rfl⟩
  | algebraMap r =>
    convert zero_mem (Ideal.span _)
    rw [sub_eq_zero]
    exact (DirectSum.decompose_of_mem_same 𝒜 r.2).symm
  | add x y hx hy _ _ =>
    rw [map_add, add_sub_add_comm]
    exact add_mem ‹_› ‹_›
  | mul x y hx hy hx' hy' =>
    convert add_mem (Ideal.mul_mem_left _ x hy')
      (Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒜 y) _ hx') using 1
    rw [map_mul]
    ring

variable [Algebra.FiniteType (𝒜 0) S]

open CategoryTheory

lemma foo : ValuativeCriterion.Existence (Proj.toSpecZero 𝒜) := by
  rintro ⟨A, K, i₁, i₂, w⟩
  obtain ⟨ι, x, _, hx, hx'⟩ := FG_by_homogeneous 𝒜
  choose d hd hxd using hx'
  have : i₁.base (IsLocalRing.closedPoint K) ∈ (⊤ : (Proj 𝒜).Opens) := trivial
  rw [← Proj.iSup_basicOpen_eq_top' 𝒜 x (fun i ↦ ⟨_, hxd i⟩) hx,
    TopologicalSpace.Opens.mem_iSup] at this
  obtain ⟨i, hi⟩ := this
  have : Set.range i₁.base ⊆ (Proj.awayι 𝒜 _ (hxd i) (hd i)).opensRange := by
    rw [Proj.opensRange_awayι]
    rintro _ ⟨x, rfl⟩
    obtain rfl := Subsingleton.elim x (IsLocalRing.closedPoint K)
    exact hi
  let φ : Spec (.of K) ⟶ _ := IsOpenImmersion.lift _ _ this
  obtain ⟨x₀, e, he, hxe, φ', hφ, hφ'⟩ :=
    projective_implies_proper_aux 𝒜 ι x hx i (A := A) (K := K) (Spec.preimage φ) d hd hxd
  let φ'' := lift_of_range_sub_range_of_injective hφ' (IsFractionRing.injective _ _)
  refine ⟨⟨Spec.map (CommRingCat.ofHom φ'') ≫ Proj.awayι 𝒜 _ hxe he, ?_, ?_⟩⟩
  · rw [← Spec.map_comp_assoc]
    convert IsOpenImmersion.lift_fac _ _ this using 1
    show _ = φ ≫ _
    rw [← Spec.map_preimage φ, ← hφ]
    convert_to Spec.map (CommRingCat.ofHom (map2 𝒜 (hxd i) (mul_comm _ _)) ≫ CommRingCat.ofHom φ') ≫
      Proj.awayι 𝒜 x₀ hxe he = _
    · congr 2; ext; exact lift_aux_spec hφ' _
    show _ = Spec.map (CommRingCat.ofHom (map2 𝒜 hxe rfl) ≫ CommRingCat.ofHom φ') ≫ _
    rw [Spec.map_comp_assoc, Spec.map_comp_assoc]
    congr 1
    rw [SpecMap_awayMap_awayι, SpecMap_awayMap_awayι]
    rfl
  · simp only [Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    conv_rhs => rw [← Spec.map_preimage i₂]
    congr 1
    ext x
    apply IsFractionRing.injective A K
    refine (lift_aux_spec hφ' _).trans ?_
    show φ' (map2 _ _ _ (HomogeneousLocalization.fromZeroRingHom 𝒜 _ _)) = _
    rw [map2_fromZeroRingHom, ← map2_fromZeroRingHom 𝒜 hxe, ← RingHom.comp_apply, hφ]
    show (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom 𝒜 _) ≫
      Spec.preimage φ) x = (Spec.preimage i₂ ≫ CommRingCat.ofHom (algebraMap A K)) x
    congr 1
    apply Spec.map_injective
    simp only [Spec.map_comp, Spec.map_preimage, ← w.w]
    rw [← Proj.awayι_toSpecZero, IsOpenImmersion.lift_fac_assoc]

instance : UniversallyClosed (Proj.toSpecZero 𝒜) := by
  rw [UniversallyClosed.eq_valuativeCriterion]
  refine ⟨foo 𝒜, ?_⟩
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]
  obtain ⟨ι, x, _, hx, hx'⟩ := FG_by_homogeneous 𝒜
  choose d hd hxd using hx'
  have H (i) : IsCompact (Proj.basicOpen 𝒜 (x i)).1 := by
    rw [← Proj.opensRange_awayι _ _ (hxd i) (hd i)]
    exact isCompact_range (Proj.awayι _ _ (hxd i) (hd i)).continuous
  have := congr($(Proj.iSup_basicOpen_eq_top' 𝒜 x (fun i ↦ ⟨_, hxd i⟩) hx).1)
  simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
    TopologicalSpace.Opens.coe_mk, TopologicalSpace.Opens.coe_top] at this
  rw [← isCompact_univ_iff, ← this]
  exact isCompact_iUnion H

instance : LocallyOfFiniteType (Proj.toSpecZero 𝒜) := by
  obtain ⟨ι, x, _, hx, hx'⟩ := FG_by_homogeneous 𝒜
  choose d hd hxd using hx'
  rw [IsLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFiniteType) _
    (Proj.iSup_basicOpen_eq_top' 𝒜 x (fun i ↦ ⟨_, hxd i⟩) hx)]
  intro i
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType)
    (Proj.basicOpenIsoSpec 𝒜 (x i) (hxd i) (hd i)).inv, ← Category.assoc, ← Proj.awayι,
    Proj.awayι_toSpecZero, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact HomogeneousLocalization.Away.finiteType _ _ _ (hxd i) (hd i)

instance : Scheme.IsSeparated (Proj 𝒜) := sorry -- in mathlib

instance : IsProper (Proj.toSpecZero 𝒜) where
