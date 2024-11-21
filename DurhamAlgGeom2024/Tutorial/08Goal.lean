import DurhamAlgGeom2024.Tutorial.«07Proper»

variable {R₀ S : Type}
variable [CommRing R₀] [CommRing S] [Algebra R₀ S]
variable (𝒜 : ℕ → Submodule R₀ S) [GradedAlgebra 𝒜]

open AlgebraicGeometry CategoryTheory

section alreadyInMathlib

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

/-- The isomorphism `D₊(f) ×[Proj 𝒜] D₊(g) ≅ D₊(fg)`. -/
noncomputable
def pullbackAwayιIso :
    Limits.pullback (awayι 𝒜 f f_deg hm) (awayι 𝒜 g g_deg hm') ≅
      Spec (CommRingCat.of (Away 𝒜 x)) :=
    IsOpenImmersion.isoOfRangeEq (Limits.pullback.fst _ _ ≫ awayι 𝒜 f f_deg hm)
      (awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m'))) <| by
  rw [IsOpenImmersion.range_pullback_to_base_of_left]
  show ((awayι 𝒜 f _ _).opensRange ⊓ (awayι 𝒜 g _ _).opensRange).1 = (awayι 𝒜 _ _ _).opensRange.1
  rw [opensRange_awayι, opensRange_awayι, opensRange_awayι, ← basicOpen_mul, hx]

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_hom_awayι :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg) (hm.trans_le (m.le_add_right m')) =
      Limits.pullback.fst _ _ ≫ awayι 𝒜 f f_deg hm :=
  IsOpenImmersion.isoOfRangeEq_hom_fac ..

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_hom_SpecMap_awayMap_left :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      Spec.map (CommRingCat.ofHom (map2 𝒜 g_deg hx)) = Limits.pullback.fst _ _ := by
  rw [← cancel_mono (awayι 𝒜 f f_deg hm), ← pullbackAwayιIso_hom_awayι,
    Category.assoc, SpecMap_awayMap_awayι]

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_hom_SpecMap_awayMap_right :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      Spec.map (CommRingCat.ofHom (map2 𝒜 f_deg (hx.trans (mul_comm _ _)))) =
      Limits.pullback.snd _ _ := by
  rw [← cancel_mono (awayι 𝒜 g g_deg hm'), ← Limits.pullback.condition,
    ← pullbackAwayιIso_hom_awayι 𝒜 f_deg hm g_deg hm' hx,
    Category.assoc, SpecMap_awayMap_awayι]
  rfl

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_inv_fst :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).inv ≫ Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (map2 𝒜 g_deg hx)) := by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_left, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
lemma pullbackAwayιIso_inv_snd :
    (pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).inv ≫ Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (map2 𝒜 f_deg (hx.trans (mul_comm _ _)))) := by
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_right, Iso.inv_hom_id_assoc]

open Scheme CategoryTheory Limits pullback HomogeneousLocalization

/-- Given `x = f * g` with `g` homogeneous of positive degree,
this is the map `A_{(f)} → A_{(x)}` taking `a/f^i` to `ag^i/(fg)^i`. -/
noncomputable
def awayMapₐ : Away 𝒜 f →ₐ[𝒜 0] Away 𝒜 x where
  __ := map2 𝒜 g_deg hx
  commutes' _ := map2_fromZeroRingHom ..

@[simp] lemma awayMapₐ_apply (a) : awayMapₐ 𝒜 g_deg hx a = map2 𝒜 g_deg hx a := rfl

lemma lift_awayMapₐ_awayMapₐ_surjective {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {d e : ℕ} {f : A} (hf : f ∈ 𝒜 d)
    {g : A} (hg : g ∈ 𝒜 e) {x : A} (hx : x = f * g) (hd : 0 < d) :
    letI : IsScalarTower (𝒜 0) (𝒜 0) (Away 𝒜 x) := IsScalarTower.of_algebraMap_smul fun _ ↦ congrFun rfl
    letI : IsScalarTower (𝒜 0) (𝒜 0) (Away 𝒜 f) := IsScalarTower.of_algebraMap_smul fun _ ↦ congrFun rfl
    Function.Surjective
      (Algebra.TensorProduct.lift (awayMapₐ 𝒜 hg hx) (awayMapₐ 𝒜 hf (hx.trans (mul_comm _ _)))
        (fun _ _ ↦ .all _ _)) := by
  intro z
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb'⟩, ⟨j, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective z
  by_cases hfg : (f * g) ^ j = 0
  · use 0
    have := HomogeneousLocalization.subsingleton 𝒜 (x := Submonoid.powers x) ⟨j, hx ▸ hfg⟩
    exact this.elim _ _
  have : n = j * (d + e) := by
    apply DirectSum.degree_eq_of_mem_mem 𝒜 hb'
    convert SetLike.pow_mem_graded _ _ using 2
    · infer_instance
    · exact hx ▸ SetLike.mul_mem_graded hf hg
    · exact hx ▸ hfg
  let x0 : NumDenSameDeg 𝒜 (.powers f) :=
  { deg := j * (d * (e + 1))
    num := ⟨a * g ^ (j * (d - 1)), by
      convert SetLike.mul_mem_graded ha (SetLike.pow_mem_graded _ hg) using 2
      rw [this]
      cases d
      · contradiction
      · simp; ring⟩
    den := ⟨f ^ (j * (e + 1)), by convert SetLike.pow_mem_graded _ hf using 2; ring⟩
    den_mem := ⟨_,rfl⟩ }
  let y0 : NumDenSameDeg 𝒜 (.powers g) :=
  { deg := j * (d * e)
    num := ⟨f ^ (j * e), by convert SetLike.pow_mem_graded _ hf using 2; ring⟩
    den := ⟨g ^ (j * d), by convert SetLike.pow_mem_graded _ hg using 2; ring⟩
    den_mem := ⟨_,rfl⟩ }
  use mk x0 ⊗ₜ mk y0
  ext
  simp only [Algebra.TensorProduct.lift_tmul, awayMapₐ_apply, val_mul,
    val_map2_mk, Localization.mk_mul, val_mk, x0, y0]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, one_mul, Submonoid.mk_mul_mk]
  cases d
  · contradiction
  · simp only [hx, add_tsub_cancel_right]
    ring

set_option maxHeartbeats 0 in
open TensorProduct in
instance isSeparated : IsSeparated (toSpecZero 𝒜) := by
  refine ⟨IsLocalAtTarget.of_openCover (Pullback.openCoverOfLeftRight
    (affineOpenCover 𝒜).openCover (affineOpenCover 𝒜).openCover _ _) ?_⟩
  intro ⟨i, j⟩
  dsimp [Scheme, Cover.pullbackHom]
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (f := (pullbackDiagonalMapIdIso ..).inv) _).mp ?_
  let e₁ : pullback ((affineOpenCover 𝒜).map i ≫ toSpecZero 𝒜)
        ((affineOpenCover 𝒜).map j ≫ toSpecZero 𝒜) ≅
        Spec (.of <| TensorProduct (𝒜 0) (Away 𝒜 i.2) (Away 𝒜 j.2)) := by
    refine pullback.congrHom ?_ ?_ ≪≫ pullbackSpecIso (𝒜 0) (Away 𝒜 i.2) (Away 𝒜 j.2)
    · simp [Proj.affineOpenCover, Proj.openCoverOfISupEqTop, awayι_toSpecZero]; rfl
    · simp [Proj.affineOpenCover, Proj.openCoverOfISupEqTop, awayι_toSpecZero]; rfl
  let e₂ : pullback ((affineOpenCover 𝒜).map i) ((affineOpenCover 𝒜).map j) ≅
        Spec (.of <| (Away 𝒜 (i.2 * j.2))) :=
    pullbackAwayιIso 𝒜 _ _ _ _ rfl
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ e₁.hom,
    ← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) e₂.inv]
  letI : IsScalarTower (𝒜 0) (𝒜 0) (Away 𝒜 i.2.1) := IsScalarTower.of_algebraMap_smul fun _ ↦ congrFun rfl
  letI : IsScalarTower (𝒜 0) (𝒜 0) (Away 𝒜 j.2.1) := IsScalarTower.of_algebraMap_smul fun _ ↦ congrFun rfl
  letI : IsScalarTower (𝒜 0) (𝒜 0) (Away 𝒜 <| i.2.1 * j.2.1) := IsScalarTower.of_algebraMap_smul fun _ ↦ congrFun rfl
  let F : Away 𝒜 i.2.1 ⊗[𝒜 0] Away 𝒜 j.2.1 →+* Away 𝒜 (i.2.1 * j.2.1) :=
    (Algebra.TensorProduct.lift (awayMapₐ 𝒜 j.2.2 rfl) (awayMapₐ 𝒜 i.2.2 (mul_comm _ _))
      (fun _ _ ↦ .all _ _)).toRingHom
  have : Function.Surjective F := lift_awayMapₐ_awayMapₐ_surjective 𝒜 i.2.2 j.2.2 rfl i.1.2
  convert IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (R := Away 𝒜 i.2.1 ⊗[𝒜 0] Away 𝒜 j.2.1) F) this using 1
  rw [← cancel_mono (pullbackSpecIso ..).inv]
  apply pullback.hom_ext
  · simp only [Iso.trans_hom, congrHom_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      limit.lift_π, id_eq, eq_mpr_eq_cast, PullbackCone.mk_pt, PullbackCone.mk_π_app, e₂, e₁,
      pullbackDiagonalMapIdIso_inv_snd_fst, AlgHom.toRingHom_eq_coe, pullbackSpecIso_inv_fst,
      ← Spec.map_comp]
    erw [pullbackAwayιIso_inv_fst]
    congr 1
    ext x
    exact DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeLeft
      (awayMapₐ 𝒜 j.2.2 rfl) (awayMapₐ 𝒜 i.2.2 (mul_comm _ _)) (fun _ _ ↦ .all _ _)).symm x
  · simp only [Iso.trans_hom, congrHom_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      limit.lift_π, id_eq, eq_mpr_eq_cast, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      pullbackDiagonalMapIdIso_inv_snd_snd, AlgHom.toRingHom_eq_coe, pullbackSpecIso_inv_snd, ←
      Spec.map_comp, e₂, e₁]
    erw [pullbackAwayιIso_inv_snd]
    congr 1
    ext x
    exact DFunLike.congr_fun (Algebra.TensorProduct.lift_comp_includeRight
      (awayMapₐ 𝒜 j.2.2 rfl) (awayMapₐ 𝒜 i.2.2 (mul_comm _ _)) (fun _ _ ↦ .all _ _)).symm x

@[stacks 01MC]
instance : Scheme.IsSeparated (Proj 𝒜) :=
  (HasAffineProperty.iff_of_isAffine (P := @IsSeparated)).mp (isSeparated 𝒜)

end alreadyInMathlib

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

instance : IsProper (Proj.toSpecZero 𝒜) where
