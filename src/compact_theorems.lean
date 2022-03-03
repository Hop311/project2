
import topology_tools

universes u v
variables {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]

/-- Proof that the product of two compact sets is itself compact. -/
theorem prod_of_compact {U : set X} {V : set Y} (hU : is_compact U) (hV : is_compact V) : is_compact (U ×ˢ V) :=
begin
  apply is_compact_of_finite_subcover', intro C,
  have h₁ : ∀ x : U, ∃ t : finset V, V ⊆ ⋃ (y : V) (_ : y ∈ t), (C.rect x.2 y.2).V,
  { intro x,
    let D : cover V := {
      ι      := V,
      sι     := λ y, (C.rect x.2 y.2).V,
      hopen  := λ _, rect.hV _,
      hcover := λ y hy, set.mem_Union.mpr ⟨⟨y, hy⟩, (rect.hp _).2⟩
    },
    exact D.has_finite_subcover_of_compact hV },
  have h₂ : ∃ t : finset U, U ⊆ ⋃ (x : U) (_ : x ∈ t), ⋂ (y : V) (_ : y ∈ (h₁ x).some), (C.rect x.2 y.2).U,
  { let D : cover U := {
      ι      := U,
      sι     := λ x, ⋂ (y : V) (_ : y ∈ (h₁ x).some), (C.rect x.2 y.2).U,
      hopen  := λ x, is_open_bInter (h₁ x).some.finite_to_set $ λ _ _, rect.hU _,
      hcover := λ x hx, set.mem_Union.mpr ⟨⟨x, hx⟩, set.mem_Inter₂.mpr $ λ _ _, (rect.hp _).1⟩
    },
    exact D.has_finite_subcover_of_compact hU },
  cases h₂ with fx hfx, classical,
  use finset.bUnion fx (λ x : U, ((h₁ x).some.1.map $ λ y : V, (C.rect x.2 y.2).j).to_finset),
  intros p hp,
  rcases set.mem_Union₂.mp (hfx hp.1) with ⟨x, hx, hp₁⟩,
  rcases set.mem_Union₂.mp ((h₁ x).some_spec hp.2) with ⟨y, hy, hp₂⟩,
  let R := C.rect x.2 y.2,
  apply set.mem_Union₂.mpr,
  exact ⟨R.j, 
    finset.mem_bUnion.mpr ⟨x, hx, multiset.mem_to_finset.mpr $ multiset.mem_map.mpr ⟨y, hy, rfl⟩⟩,
    R.hj ⟨(set.mem_Inter₂.mp hp₁ y hy : _), hp₂⟩⟩
end

/-- Proof that if the product of two nonempty sets is compact, so are the two sets. -/
theorem compact_of_prod {U : set X} {V : set Y} (hU : U.nonempty) (hV : V.nonempty) (hUV : is_compact (U ×ˢ V)) :
  is_compact U ∧ is_compact V :=
    ⟨prod_image_fst U hV ▸ (hUV.image_of_continuous_on continuous_on_fst),
      prod_image_snd hU V ▸ (hUV.image_of_continuous_on continuous_on_snd)⟩

/-- Proof that if the nonempty product of two sets is compact, so are the two sets. -/
theorem compact_of_prod' {U : set X} {V : set Y} : set.nonempty (U ×ˢ V) → is_compact (U ×ˢ V) →
  is_compact U ∧ is_compact V := λ ⟨p, hp⟩, compact_of_prod ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩

/-- Proof that for a compact set `U` and any set `V`, the projection map
  `U × V → V` preserves closed sets. -/
theorem proj_closed_of_compact {U : set X} (hU : is_compact U) : ∀ (V : set Y),
  is_closed_map (prod.snd : U × V → V) :=
begin
  intros V C hC,
  apply is_closed_iff_outside_neighbourhoods.mpr,
  intros y hy,
  let D : cover U := {
    ι      := {U' : set X // is_open U' ∧ ∃ W : set Y, is_open W ∧
      y.1 ∈ W ∧ ∀ p ∈ C, ((p.1.1, p.2.1) : X × Y) ∉ U' ×ˢ W},
    sι     := subtype.val,
    hopen  := λ i, i.2.1,
    hcover := begin
      intros x hx, let x' : U := ⟨x, hx⟩, let p := (x', y),
      apply set.mem_Union.mpr,
      rcases is_closed_iff_outside_neighbourhoods.mp hC p (λ h, hy ⟨p, h, rfl⟩) with ⟨R, hR, hpR, hCR⟩,
      rcases is_open_prod_iff.mp hR x' y hpR with ⟨U', V', hU', hV', hxU', hyV', hUV'⟩,
      rcases is_open_subtype.mp hU' with ⟨S, hS, hUS'⟩,
      rcases is_open_subtype.mp hV' with ⟨T, hT, hVT'⟩,
      exact ⟨⟨S, hS, T, hT, (hVT' y).mp hyV', λ q hq ⟨h₁, h₂⟩, by {
        have : q ∈ C ∩ R := ⟨hq, hUV' ⟨(hUS' q.1).mpr h₁, (hVT' q.2).mpr h₂⟩⟩,
        rw [hCR] at this, exact this }⟩, (hUS' x').mp hxU'⟩
    end },
  cases D.has_finite_subcover_of_compact hU with Dι hDι,
  let W := ⋂ (i : D.ι) (_ : i ∈ Dι), i.2.2.some,
  have hW := is_open_bInter Dι.finite_to_set (λ i _, i.2.2.some_spec.1),
  have hyW : y.1 ∈ W := set.mem_bInter (λ i _, i.2.2.some_spec.2.1),
  have hWC : ∀ p : U × V, p.2.1 ∈ W → p ∉ C,
  { intros p hp hpC,
    rcases set.mem_Union₂.mp (hDι p.1.2) with ⟨i, hi, hpi⟩,
    exact i.2.2.some_spec.2.2 p hpC ⟨hpi, (set.mem_Inter₂.mp hp i hi : _)⟩ },
  exact ⟨{y : V | y.1 ∈ W}, is_open_subtype.mpr ⟨W, hW, λ _, iff.rfl⟩, hyW, by
  { ext y', apply (iff_false _).mpr, apply not_and.mpr,
    intros hyC' hyW', rcases hyC' with ⟨p', hpC', hpy'⟩,
    exact absurd hpC' (hWC p' (hpy'.symm ▸ hyW')) }⟩
end

/-- Space consisting of an embedding of `U` and a single distinguished point `pt`. -/
inductive pt_space (U : set X)
| pt  : pt_space
| emb : U → pt_space

open pt_space

/-- A topology on `pt_space U` with opens:
  • the embedding of any subset of `U` (regardless of whether it's open or not),
  • for all `i` in the indexing type `ι`, `pt` unioned with the embedding of `sι i`.
  This is not an instance as it requires the set `U` and the collection of sets `sι` as arguments. -/
def pt_space_topology (U : set X) {ι : Type u} (sι : ι → set X) : topological_space (pt_space U) := {
  is_open := λ s, pt ∉ s ∨ ∃ t : finset ι, ∀ x : U, (x.1 ∈ ⋂ i ∈ t, sι i) → emb x ∈ s,
  is_open_univ := or.inr ⟨∅, λ _ _, trivial⟩,
  is_open_inter := begin
    intros s t hs ht,
    cases hs with hs hs,
    { exact or.inl (λ h, hs h.1) },
    { cases ht with ht ht,
      { exact or.inl (λ h, ht h.2) },
      { apply or.inr, cases hs with fs hs, cases ht with ft ht, classical,
        exact ⟨fs ∪ ft, λ x hx, ⟨hs x $ finset_intersection_subset (finset.subset_union_left fs ft) hx,
          ht x $ finset_intersection_subset (finset.subset_union_right fs ft) hx⟩⟩ } }
  end,
  is_open_sUnion := begin
    intros s hs,
    by_cases h : ∀ t ∈ s, pt ∉ t,
    { apply or.inl, intro h',
      rcases set.mem_sUnion.mp h' with ⟨t, hts, hptt⟩,
      exact absurd hptt (h t hts) },
    { simp only [not_forall] at h,
      rcases h with ⟨t, hts, hptt⟩,
      cases (hs t hts).resolve_left hptt with fs h,
      exact or.inr ⟨fs, λ x hx, set.mem_sUnion.mpr ⟨t, hts, h x hx⟩⟩ }
  end
}

/-- The set `sι i ∪ {pt}` in `pt_space`. -/
def pt_embedding (U : set X) {ι : Type u} (sι : ι → set X) (i : ι) : set (pt_space U) :=
  {x | x = pt ∨ ∃ x' : U, x'.1 ∈ sι i ∧ x = emb x'}

/-- Proof that the set `sι i ∪ {pt}` is open in `pt_space_topology`. -/
theorem pt_embedding.is_open (U : set X) {ι : Type u} (sι : ι → set X) (i : ι) :
  @is_open _ (pt_space_topology U sι) (pt_embedding U sι i) :=
begin
  apply or.inr, use {i}, intros x hx,
  simp only [finset.mem_singleton, set.Inter_Inter_eq_left] at hx,
  exact or.inr ⟨x, hx, rfl⟩
end

/-- If the topology inducing collection of sets `sι` satisfies the finite intersection property,
  then the singleton `{pt}` cannot be open in `pt_space_topology`. -/
theorem pt_nonempty {U : set X} {ι : Type u} {sι : ι → set X}
  (hfip : ∀ t : finset ι, (U ∩ ⋂ i ∈ t, sι i).nonempty) : ¬@is_open _ (pt_space_topology U sι) {pt} :=
begin
  intro h,
  cases h.resolve_left (not_not.mpr (set.mem_singleton pt)) with t ht,
  cases hfip t with x hx,
  apply not_not.mpr (set.mem_singleton_iff.mp (ht ⟨x, hx.1⟩ hx.2)),
  apply pt_space.no_confusion
end

/-- Wrapper for explicit use of the subtype topology instance. -/
def subtype_topology {X : Type u} (_ : topological_space X) (U : set X) :
  topological_space U := infer_instance

/-- Wrapper for explicit use of the product topology instance. -/
def product_topology {X : Type u} {Y : Type v} (_ : topological_space X) (_ : topological_space Y) :
  topological_space (X × Y) := infer_instance

/-- If a set `U` satisfies, for any set `V`, the projection map `U × V → V` is closed, then `U` is compact.  -/
theorem compact_of_proj_closed {U : set X} (h : ∀ {Y : Type u} {ty : topological_space Y} (V : set Y),
  @is_closed_map _ _ (product_topology infer_instance (subtype_topology ty V)) (subtype_topology ty V)
    (prod.snd : U × V → V)) : is_compact U :=
begin
  apply is_compact_iff_finite_intersection_property.mpr,
  intros ι sι hι hfip,
  let pt_sp := pt_space U,
  let top₀  := pt_space_topology U sι,
  let top₁  := subtype_topology top₀ set.univ,
  let top₂  : topological_space (U × @set.univ pt_sp) := product_topology infer_instance top₁,
  let K     := @closure _ top₂ {p | p.2.1 = emb p.1},
  have : (prod.snd '' K)ᶜ ⊆ {⟨pt, trivial⟩},
  { rintros ⟨x, _⟩ hx,
    simp only [set.mem_compl_eq, set.mem_image, not_exists, not_and] at hx,
    cases x,
    { exact set.mem_singleton_iff.mpr rfl },
    { have := hx ⟨x, emb x, trivial⟩ (by { apply subset_closure, change _ = _, refl }),
      exfalso, apply this, refl } },
  have : (⟨pt, trivial⟩ : @set.univ pt_sp) ∈ prod.snd '' K,
  { cases set.subset_singleton_iff_eq.mp this with he he,
    { rw [set.compl_empty_iff.mp he], trivial },
    { have : @is_closed _ top₁ (prod.snd '' K) := h set.univ K (@is_closed_closure _ top₂ _),
      have : @is_open _ top₁ {⟨pt, trivial⟩} := he ▸ ((@is_open_compl_iff _ top₁ _).mpr this),
      cases (@is_open_subtype _ top₀ _ _).mp this with T hT,
      have : T = {pt},
      { ext x, have := hT.2 ⟨x, trivial⟩, rw [set.mem_singleton_iff] at this ⊢,
        cases x; { simp only [eq_self_iff_true, subtype.mk_eq_mk] at this ⊢, exact this.symm } },
      exact absurd (this ▸ hT.1 : @is_open _ top₀ {pt}) (pt_nonempty hfip) } },
  rcases this with ⟨p, hpK, hpe⟩,
  have : ∀ i : ι, p.1.1 ∈ sι i,
  { intro i,
    have := (@mem_closure_iff _ top₂ _ _).mp hpK (@set.univ U ×ˢ {x : set.univ | x.1 ∈ pt_embedding U sι i})
      ((@is_open.prod _ _ _ top₁ _ _) is_open_univ $ (@is_open_subtype _ top₀ _ _).mpr
        ⟨pt_embedding U sι i, pt_embedding.is_open U sι i, λ x, iff.rfl⟩) ⟨trivial, hpe.symm ▸ or.inl rfl⟩,
    rcases this with ⟨p', ⟨_, hp'⟩, (hpD' : _ = _)⟩,
    rcases hp'.resolve_left (by { rw [hpD'], apply pt_space.no_confusion }) with ⟨x, hxi, hxe⟩,
    by_contra hi,
    rcases is_closed_iff_outside_neighbourhoods.mp (hι i) p.1.1 hi with ⟨V, hV, hpV, hiV⟩,
    have := (@mem_closure_iff _ top₂ _ _).mp hpK ({x : U | x.1 ∈ V} ×ˢ {x : set.univ | x.1 ∈ pt_embedding U sι i})
      ((@is_open.prod _ _ _ top₁ _ _) (is_open_subtype.mpr ⟨V, hV, λ x, iff.rfl⟩) $ (@is_open_subtype _ top₀ _ _).mpr
        ⟨pt_embedding U sι i, pt_embedding.is_open U sι i, λ x, iff.rfl⟩) ⟨hpV, or.inl $ congr_arg subtype.val hpe⟩,
    rcases this with ⟨x', ⟨hxV', hxi'⟩, (hxD' : _ = _)⟩,
    rcases hxi'.resolve_left (by { rw [hxD'], apply pt_space.no_confusion }) with ⟨x'', hxi'', hxe''⟩,
    apply set.not_nonempty_iff_eq_empty.mpr hiV,
    exact ⟨x'.1.1, emb.inj (hxe''.symm.trans hxD') ▸ hxi'', hxV'⟩ },
  exact ⟨p.1.1, p.1.2, set.mem_Inter.mpr this⟩
end

/-- A set `U` is compact if and only if for every set `V`, the projection map `U × V → V` is closed. -/
theorem compact_iff_proj_closed {U : set X} : is_compact U ↔ (∀ {Y : Type u} {ty : topological_space Y} (V : set Y),
  @is_closed_map _ _ (product_topology infer_instance (subtype_topology ty V)) (subtype_topology ty V)
    (prod.snd : U × V → V)) := ⟨λ h Y topY V, @proj_closed_of_compact _ _ _ topY U h V, compact_of_proj_closed⟩
