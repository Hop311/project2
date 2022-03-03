
import topology.constructions
import topology.subset_properties
import topology.maps

universes u v
variables {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]

section cover
  /-- Structure representing a cover of `U` made up of open sets `sι` indexed by type `ι`. -/
  structure cover (U : set X) :=
  (ι      : Type u)
  (sι     : ι → set X)
  (hopen  : ∀ i, is_open (sι i))
  (hcover : U ⊆ ⋃ i, sι i)

  /-- For any point `x` in `U` and any cover `C` of `U`, there must exist some open set in `C` containing `x`. -/
  theorem cover.mem {U : set X} (C : cover U) {x : X} (hx : x ∈ U) : ∃ i : C.ι, x ∈ C.sι i :=
    set.mem_Union.mp $ C.hcover hx

  /-- A Prop stating that the cover `C` of `U` can cover `U` with the union of `sι i` for finitely many `i : ι`. -/
  def cover.has_finite_subcover {U : set X} (C : cover U) : Prop := ∃ t : finset C.ι, U ⊆ ⋃ i ∈ t, C.sι i

  /-- A cover with a finite subcover is compact. -/
  theorem is_compact_of_finite_subcover' {U : set X} (h : ∀ C : cover U, C.has_finite_subcover) : is_compact U :=
    is_compact_of_finite_subcover $ λ ι sι hopen hcover, h $ cover.mk ι sι hopen hcover

  /-- Any cover of a compact set has a finite subcover. -/
  theorem cover.has_finite_subcover_of_compact {U : set X} (hU : is_compact U) (C : cover U) :
    C.has_finite_subcover := hU.elim_finite_subcover C.sι C.hopen C.hcover

  /-- For a point `p` in the product space `X × Y` and a cover `C` of the set `U' ×ˢ V'`, this structure
    requires that `p` belong to the set `U ×ˢ V` for `U` and `V` open, with `U ×ˢ V` wholly contained in
    the open indexed by `j` in `C`.  -/
  structure rect {U' : set X} {V' : set Y} (C : cover (U' ×ˢ V')) (p : X × Y) :=
  (U  : set X)     (V  : set Y)
  (hU : is_open U) (hV : is_open V)
  (j  : C.ι)       (hj : U ×ˢ V ⊆ C.sι j)
  (hp : p ∈ U ×ˢ V)

  /-- Coercion to the product of open sets `U ×ˢ V` that define a rect. -/
  instance rect.to_set {U' : set X} {V' : set Y} (C : cover (U' ×ˢ V')) (p : X × Y) : has_coe (rect C p) (set (X × Y)) :=
    ⟨λ r, r.U ×ˢ r.V⟩

  /-- Proof that the product of open sets `U ×ˢ V` is open in the product toplogy. -/
  theorem rect.is_open {U' : set X} {V' : set Y} {C : cover (U' ×ˢ V')} {p : X × Y} (R : rect C p) :
    is_open (R : set (X × Y)) := is_open.prod R.hU R.hV

  /-- Function which, given any product `U × V` containing a point `p` and a cover `C`,
    produces a rect with respect to the point and cover. -/
  noncomputable def cover.rect {U : set X} {V : set Y} (C : cover (U ×ˢ V))
    {x : X} (hx : x ∈ U) {y : Y} (hy : y ∈ V) : rect C (x, y) :=
  begin
    have hp : (x, y) ∈ U ×ˢ V := ⟨hx, hy⟩,
    -- cannot use cases/rcases for non-Props, as the goal is not a Prop
    let j  := (C.mem hp).some,
    have   := is_open_prod_iff.mp (C.hopen j) x y (C.mem hp).some_spec,
    let U' := this.some,
    let V' := this.some_spec.some,
    rcases this.some_spec.some_spec with ⟨hU', hV', hx, hy, hj⟩,
    exact rect.mk U' V' hU' hV' j hj ⟨hx, hy⟩
  end
end cover

/-- The left projection out of `U ×ˢ V` is equal to `U`. -/
theorem prod_image_fst {X : Type*} {Y : Type*} (U : set X)  {V : set Y} (hV : V.nonempty) : prod.fst '' (U ×ˢ V) = U :=
begin
  ext x, exact ⟨λ ⟨p, hp, hx⟩, hx ▸ hp.1, λ hx, by
    { cases hV with y hy, exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩ } ⟩
end

/-- The right projection out of `U ×ˢ V` is equal to `V`. -/
theorem prod_image_snd {X : Type*} {Y : Type*} {U : set X}  (hU : U.nonempty) (V : set Y) : prod.snd '' (U ×ˢ V) = V :=
begin
  ext y, exact ⟨λ ⟨p, hp, hy⟩, hy ▸ hp.2, λ hy, by
    { cases hU with x hx, exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩ } ⟩
end

/-- A set is closed if and only if every point out side it has an open neighbourhood. -/
theorem is_closed_iff_outside_neighbourhoods {U : set X} : is_closed U ↔ ∀ x ∉ U,
  ∃ U' : set X, is_open U' ∧ x ∈ U' ∧ U ∩ U' = ∅ :=
begin
  rw [is_closed_iff_nhds], split,
  { intros h x hx,
    have := mt (h x) hx, simp only [not_forall] at this,
    rcases this with ⟨U₁, hU₁, hUU₁⟩,
    rcases mem_nhds_iff.mp hU₁ with ⟨U₂, hU₂U₁, hU₂, hxU₂⟩,
    exact ⟨U₂, hU₂, hxU₂, set.ext $ λ y, ⟨λ ⟨hyU, hyU₂⟩, hUU₁ ⟨y, hU₂U₁ hyU₂, hyU⟩, false.elim⟩⟩ },
  { intros h x h', by_contra hx,
    rcases h x hx with ⟨U', hU', hxU', hUU'⟩,
    rw [set.inter_comm] at hUU',
    exact absurd hUU' (h' U' (hU'.mem_nhds hxU')).ne_empty }
end

/-- A set in the subtype (subset) topology of `U` is open if and only if it is the intersection
  of an open set(in the topology of `X`) with `U`. -/
theorem is_open_subtype {U : set X} {S : set U} : is_open S ↔ ∃ T : set X, is_open T ∧
  ∀ x : U, x ∈ S ↔ x.1 ∈ T :=
begin
  rw [is_open_induced_iff],
  have : ∀ T : set X, (coe ⁻¹' T = S) ↔ ∀ x : U, x ∈ S ↔ x.1 ∈ T,
  { intros, split,
    { intros h _, rw [←h], refl },
    { intro h, ext x, rw [h x], refl } },
  exact ⟨λ ⟨T, h₁, h₂⟩, ⟨T, h₁, (this T).mp h₂⟩, λ ⟨T, h₁, h₂⟩, ⟨T, h₁, (this T).mpr h₂⟩⟩
end

/-- A set `U` is compact if and only if every collection of closed sets satisfying the
  finite intersection property, i.e. the intersection of finitely many such sets is nonempty,
  the intersection of all of these sets is also nonempty. -/
theorem is_compact_iff_finite_intersection_property {U : set X} : is_compact U ↔
  ∀ (ι : Type u) (sι : ι → set X), (∀ i, is_closed (sι i)) → (∀ t : finset ι, (U ∩ ⋂ i ∈ t, sι i).nonempty) →
    (U ∩ ⋂ i, sι i).nonempty :=
begin
  rw [is_compact_iff_finite_subfamily_closed], split,
  { intros h ι sι hclosed,
    have := mt (h sι hclosed),
    simp only [not_exists, ←ne.def, set.ne_empty_iff_nonempty] at this,
    exact this },
  { intros h ι sι hclosed,
    rw [←not_imp_not],
    simp only [not_exists, ←ne.def, set.ne_empty_iff_nonempty],
    exact h ι sι hclosed }
end

/-- Intersection over finite indicies reverses subsets. -/
theorem finset_intersection_subset {α : Type*} {ι : Type*} {f : ι → set α} {s t : finset ι}
  (h : s ⊆ t) : (⋂ i ∈ t, f i) ⊆ (⋂ i ∈ s, f i) :=
begin
  intro, simp only [set.mem_Inter₂], exact (λ h' i hi, h' i (h hi))
end
