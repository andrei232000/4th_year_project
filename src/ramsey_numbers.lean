import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import data.finset.basic
import data.finset.card
import data.fintype.basic
import data.fintype.card
import data.finset.powerset
import simple_graph_aux
import complete_graph_aux
import coercions_aux
import induced_subgraph

universe u
variables {V : Type u} [fintype V] [decidable_eq V]
variables (G : simple_graph V) [decidable_rel G.adj]
variables {k : ℕ}

variable R : ↥(finset.powerset_len k (finset.univ : finset V))

variable red_edges : (finset ↥G.edge_finset)

variable red_edges_by_R : 
finset ↥(G.edge_finset \ ((G.induced_subgraph R).edge_finset)) ×
finset ↥((G.induced_subgraph R).edge_finset)

theorem card_R : (R : finset V).card = k :=
begin
  cases R with R R_in,
  change R.card = k,
  rw finset.mem_powerset_len at R_in,
  rw R_in.right,
end

def red_edges_by_R_coe :
( finset ↥(G.edge_finset \ ((G.induced_subgraph R).edge_finset)) ×
  finset ↥((G.induced_subgraph R).edge_finset) ) →
  (finset ↥G.edge_finset) := λ c, 
  ↑(⟨finset.map (function.embedding.subtype _) c.fst ∪
    finset.map (function.embedding.subtype _) c.snd,
    begin
      rw finset.union_subset_iff,
      split,
      { rw finset.subset_iff,
        intro x,
        intro x_in,
        have x_in' := finset.property_of_mem_map_subtype c.fst x_in,
        rw finset.mem_sdiff at x_in',
        exact x_in'.left,},
      { rw finset.subset_iff,
        intro x,
        intro x_in,
        have x_in' := finset.property_of_mem_map_subtype c.snd x_in,
        apply finset.mem_of_subset,
        exact (G.induced_subgraph R).edge_finset_subset,
        exact x_in', },
    end⟩ : {s // s ⊆ G.edge_finset})

instance red_edges_by_R_has_coe : has_coe
  ( finset ↥(G.edge_finset \ ((G.induced_subgraph R).edge_finset)) ×
    finset ↥((G.induced_subgraph R).edge_finset))
  (finset ↥G.edge_finset) 
:= ⟨red_edges_by_R_coe G R⟩

theorem red_edges_by_R_coe_inj :
function.injective (red_edges_by_R_coe G R) :=
begin
  unfold function.injective,
  unfold red_edges_by_R_coe,
  change (coe : 
    {s // s ⊆ G.edge_finset} →
      finset ↥(G.edge_finset))
    with subset_subtype.finset_subtype.coe,
  intros c₁ c₂,
  intro h_union,
  rw function.injective.eq_iff subset_subtype.finset_subtype.coe_injective
    at h_union,
  rw subtype.mk_eq_mk at h_union,
  rw prod.ext_iff,
  split,
  { rw finset.ext_iff,
    intro e,
    split,
    { intro e_in₁,
      have e_coe_in₁ := finset.mem_map_of_mem 
        (function.embedding.subtype _) e_in₁,
      rw function.embedding.coe_subtype _ at e_coe_in₁,
      have e_coe_in_union : 
        ↑e ∈ finset.map (function.embedding.subtype _) c₁.fst ∪
          finset.map (function.embedding.subtype _) c₁.snd,
      { rw finset.mem_union,
        left,
        exact e_coe_in₁, },
      rw h_union at e_coe_in_union,
      have e_coe_in₂ : 
        ↑e ∈ finset.map (function.embedding.subtype _) c₂.fst,
      { rw finset.mem_union at e_coe_in_union,
        cases e_coe_in_union with e_coe_in₂ e_coe_in_false,
        { exact e_coe_in₂, },
        { exfalso,
          have e_in_R := 
            finset.property_of_mem_map_subtype _ e_coe_in_false,
          have e_not_in_R := e.property,
          rw finset.mem_sdiff at e_not_in_R,
          exact e_not_in_R.right e_in_R, }, },
      simp only [finset.mem_sdiff, simple_graph.mem_edge_finset,
        simple_graph.complete_graph_eq_top, coe_coe, finset.mem_map,
        function.embedding.coe_subtype, exists_prop, subtype.exists, 
        subtype.coe_mk, exists_and_distrib_right, exists_eq_right, 
        finset.mk_coe] at e_coe_in₂,
      exact e_coe_in₂.right, },
    { intro e_in₂,
      have e_coe_in₂ := finset.mem_map_of_mem 
        (function.embedding.subtype _) e_in₂,
      rw function.embedding.coe_subtype _ at e_coe_in₂,
      have e_coe_in_union : 
        ↑e ∈ finset.map (function.embedding.subtype _) c₂.fst ∪
          finset.map (function.embedding.subtype _) c₂.snd,
      { rw finset.mem_union,
        left,
        exact e_coe_in₂, },
      rw ← h_union at e_coe_in_union,
      have e_coe_in₁ : 
        ↑e ∈ finset.map (function.embedding.subtype _) c₁.fst,
      { rw finset.mem_union at e_coe_in_union,
        cases e_coe_in_union with e_coe_in₁ e_coe_in_false,
        { exact e_coe_in₁, },
        { exfalso,
          have e_in_R := 
            finset.property_of_mem_map_subtype _ e_coe_in_false,
          have e_not_in_R := e.property,
          rw finset.mem_sdiff at e_not_in_R,
          exact e_not_in_R.right e_in_R,}, },
      simp only [finset.mem_sdiff, simple_graph.mem_edge_finset,
        simple_graph.complete_graph_eq_top, coe_coe, finset.mem_map,
        function.embedding.coe_subtype, exists_prop, subtype.exists,
        subtype.coe_mk, exists_and_distrib_right, exists_eq_right,
        finset.mk_coe] at e_coe_in₁,
      exact e_coe_in₁.right, }, },
  { rw finset.ext_iff,
    intro e,
    split,
    { intro e_in₁,
      have e_coe_in₁ := finset.mem_map_of_mem 
        (function.embedding.subtype _) e_in₁, 
      rw function.embedding.coe_subtype at e_coe_in₁,
      have e_coe_in_union : 
        ↑e ∈ finset.map (function.embedding.subtype _) c₁.fst ∪
          finset.map (function.embedding.subtype _) c₁.snd,
      { rw finset.mem_union,
        right,
        exact e_coe_in₁, },
      rw h_union at e_coe_in_union,
      have e_coe_in₂ : 
        ↑e ∈ finset.map (function.embedding.subtype _) c₂.snd,
      { rw finset.mem_union at e_coe_in_union,
        cases e_coe_in_union with e_coe_in_false e_coe_in₂,
        { exfalso,
          have e_not_in_R := 
            finset.property_of_mem_map_subtype _ e_coe_in_false,
          rw finset.mem_sdiff at e_not_in_R,
          have e_in_R := e.property,
          exact e_not_in_R.right e_in_R, },
        { exact e_coe_in₂, }, },
      simp only [coe_coe, finset.mem_map, function.embedding.coe_subtype,
        exists_prop, subtype.exists, subtype.coe_mk,
        exists_and_distrib_right, exists_eq_right, finset.mk_coe] 
        at e_coe_in₂,
      exact e_coe_in₂.right, },
    { intro e_in₂,
      have e_coe_in₂ := finset.mem_map_of_mem 
        (function.embedding.subtype _) e_in₂, 
      rw function.embedding.coe_subtype at e_coe_in₂,
      have e_coe_in_union : 
        ↑e ∈ finset.map (function.embedding.subtype _) c₂.fst ∪
          finset.map (function.embedding.subtype _) c₂.snd,
      { rw finset.mem_union,
        right,
        exact e_coe_in₂, },
      rw ← h_union at e_coe_in_union,
      have e_coe_in₁ : 
        ↑e ∈ finset.map (function.embedding.subtype _) c₁.snd,
      { rw finset.mem_union at e_coe_in_union,
        cases e_coe_in_union with e_coe_in_false e_coe_in₁,
        { exfalso,
          have e_not_in_R := 
            finset.property_of_mem_map_subtype _ e_coe_in_false,
          rw finset.mem_sdiff at e_not_in_R,
          have e_in_R := e.property,
          exact e_not_in_R.right e_in_R, },
        { exact e_coe_in₁, }, },
      simp only [coe_coe, finset.mem_map, function.embedding.coe_subtype,
        exists_prop, subtype.exists, subtype.coe_mk, 
        exists_and_distrib_right, exists_eq_right, finset.mk_coe] 
        at e_coe_in₁,
      exact e_coe_in₁.right, }, },
end

def A : Prop := 
∀ (e₁ : ↥((G.induced_subgraph R).edge_finset)) 
  (e₂ : ↥((G.induced_subgraph R).edge_finset)),
( set.inclusion (G.induced_subgraph R).edge_finset_subset e₁ ∈ red_edges ∧
  set.inclusion (G.induced_subgraph R).edge_finset_subset e₂ ∈ red_edges ) ∨
( set.inclusion (G.induced_subgraph R).edge_finset_subset e₁ ∉ red_edges ∧ 
  set.inclusion (G.induced_subgraph R).edge_finset_subset e₂ ∉ red_edges )

instance A_decidable : decidable_pred (A G R) := 
begin
  unfold decidable_pred,
  intro red_edges,
  unfold A,
  refine fintype.decidable_forall_fintype,
end

def finset_univ_two_colouring : finset (finset ↥(G.edge_finset)) := 
finset.univ

def two_colourings_sat_A_R : finset (finset ↥(G.edge_finset)) := 
finset.filter (A G R) (finset_univ_two_colouring G)

def empty_univ_col_R : 
finset (finset ↥(G.edge_finset \ ((G.induced_subgraph R).edge_finset)) ×
 finset ↥((G.induced_subgraph R).edge_finset)) := 
finset.product finset.univ {∅, finset.univ}

theorem all_red_colourings_sat_A_R : 
two_colourings_sat_A_R (complete_graph V) R = 
finset.map 
  ⟨red_edges_by_R_coe (complete_graph V) R, red_edges_by_R_coe_inj _ _⟩
  (empty_univ_col_R (complete_graph V) R) :=
begin
  unfold two_colourings_sat_A_R,
  unfold finset_univ_two_colouring,
  unfold empty_univ_col_R,
  unfold red_edges_by_R_coe,
  change (coe : 
    {s // s ⊆ (complete_graph V).edge_finset} → 
      finset ↥((complete_graph V).edge_finset)) 
    with subset_subtype.finset_subtype.coe,
  rw finset.ext_iff,
  intro c,
  simp only [finset.mem_filter, finset.mem_univ, true_and, finset.mem_map,
    finset.mem_product, finset.mem_insert, finset.mem_singleton, 
    function.embedding.coe_fn_mk, exists_prop, prod.exists],
  split,
  { intro hA,
    generalize h_cR : simple_graph.induced_subgraph.edge_subtype_finset
      (complete_graph V) R (finset.map (function.embedding.subtype _) c) = cR,
    use simple_graph.induced_subgraph.edge_complement_subtype_finset
      (complete_graph V) R (finset.map (function.embedding.subtype _) c),
    use cR,
    rw ← @finset.map_inj _ _ 
      (function.embedding.subtype (∈ (complete_graph V).edge_finset)) _ _,
    rw subset_subtype.coe_type,
    have h_union : 
      finset.map (function.embedding.subtype _) 
        (simple_graph.induced_subgraph.edge_complement_subtype_finset
          (complete_graph V) R 
          (finset.map (function.embedding.subtype _) c)) ∪
      finset.map (function.embedding.subtype _) cR =
      finset.map (function.embedding.subtype _) c,
    { rw ← h_cR,
      unfold simple_graph.induced_subgraph.edge_complement_subtype_finset,
      unfold simple_graph.induced_subgraph.edge_subtype_finset,
      rw finset.subtype_map,
      rw finset.subtype_map,
      simp_rw [finset.mem_sdiff],
      rw finset.union_comm,
      rw finset.filter_and,
      rw finset.union_distrib_left,
      rw finset.filter_union_filter_neg_eq 
        (∈ ((complete_graph V).induced_subgraph ↑R).edge_finset) 
          (finset.map (function.embedding.subtype _) c),
      have h_eq_c : 
        finset.filter
          (∈ (complete_graph V).edge_finset)
          (finset.map (function.embedding.subtype _) c) = 
        (finset.map (function.embedding.subtype _) c),
      { rw finset.filter_eq_self,
        intro x,
        intro x_in,
        have := finset.property_of_mem_map_subtype _ x_in,
        exact this, },
      rw h_eq_c,
      rw finset.union_comm,
      exact finset.union_inter_cancel_left, },
    cases finset.eq_empty_or_nonempty cR with cR_empty cR_nonempty,
    { clear hA,
      split,
      { left,
        exact cR_empty,},
      { exact h_union, }, },
    { split,
      { clear h_union,
        right,
        unfold finset.nonempty at cR_nonempty,
        cases cR_nonempty with e₁ e₁_in,
        apply finset.ext,
        intro e₂,
        split,
        { revert e₂,
          exact cR.subset_univ, },
        { intro e₂_in,
          specialize hA e₁ e₂,
          cases hA with h_red h_blue,
          { rw ← h_cR,
            unfold simple_graph.induced_subgraph.edge_subtype_finset,
            simp only [simple_graph.mem_edge_finset,
              simple_graph.complete_graph_eq_top, finset.mem_subtype,
                finset.mem_map, function.embedding.coe_subtype,
                exists_prop, subtype.exists, subtype.coe_mk,
                exists_and_distrib_right, exists_eq_right],
            have e₂_in_set : ↑e₂ ∈ (complete_graph V).edge_set,
            { have e₂_in_finset := finset.mem_of_subset 
                ((complete_graph V).induced_subgraph R).edge_finset_subset
                e₂.property,
              unfold simple_graph.edge_finset at e₂_in_finset,
              rw set.mem_to_finset at e₂_in_finset,
              exact e₂_in_finset, },
            use e₂_in_set,
          exact h_red.right, },
          { exfalso,
            have e₁_not_in := h_blue.left,
            rw ← hcR,
            unfold simple_graph.induced_subgraph.edge_subtype_finset 
              at e₁_in,
            simp only [simple_graph.mem_edge_finset,
              simple_graph.complete_graph_eq_top, finset.mem_subtype,
              finset.mem_map, function.embedding.coe_subtype, exists_prop,
              subtype.exists, subtype.coe_mk, exists_and_distrib_right,
              exists_eq_right] at e₁_in,
            cases e₁_in with _ e₁_in,
            exact h_blue.left e₁_in, }, }, },
        { exact h_union, }, }, },
  { rintro ⟨cRc, cR, hcR, h_union⟩,
    cases hcR with cR_empty cR_univ,
    { intros e₁ e₂,
      right,
      rw ← h_union,
      clear h_union,
      rw cR_empty,
      clear cR_empty,
      simp only [finset.map_empty, finset.union_empty],
      unfold subset_subtype.finset_subtype.coe,
      split,
      { by_contra,
        simp only [finset.univ_eq_attach, finset.mem_map,
          finset.mem_attach, function.embedding.coe_fn_mk,
          exists_true_left] at h,
        unfold set.inclusion at h,
        rcases h with ⟨⟨a, a_in⟩, h_eq⟩,
        rw subtype.mk_eq_mk at h_eq,
        change a = e₁.val at h_eq,
        rw h_eq at a_in,
        have e_in := finset.property_of_mem_map_subtype cRc a_in,
        rw finset.mem_sdiff at e_in,
        exact e_in.right e₁.property, },
      { by_contra,
        simp only [finset.univ_eq_attach, finset.mem_map,
          finset.mem_attach, function.embedding.coe_fn_mk,
          exists_true_left] at h,
        unfold set.inclusion at h,
        rcases h with ⟨⟨a, a_in⟩, h_eq⟩,
        rw subtype.mk_eq_mk at h_eq,
        change a = e₂.val at h_eq,
        rw h_eq at a_in,
        have e_in := finset.property_of_mem_map_subtype cRc a_in,
        rw finset.mem_sdiff at e_in,
        exact e_in.right e₂.property, }, },
    { intros e₁ e₂,
      left,
      rw ← h_union,
      clear h_union,
      rw cR_univ,
      clear cR_univ,
      unfold subset_subtype.finset_subtype.coe,
      simp only [finset.univ_eq_attach, finset.mem_map, finset.mem_attach,
        function.embedding.coe_fn_mk, exists_true_left],
      split,
      { use e₁,
        { rw set.mem_def,
          rw ← finset.mem_def,
          rw finset.mem_union, 
          right,
          change (function.embedding.subtype _) e₁ ∈ finset.map
              (function.embedding.subtype _) finset.univ,
          rw finset.mem_map' (function.embedding.subtype _),
          exact finset.mem_univ e₁, },
        refl, },
      { use e₂,
        { rw set.mem_def,
          rw ← finset.mem_def,
          rw finset.mem_union, 
          right,
          change (function.embedding.subtype _) e₂ ∈ finset.map 
              (function.embedding.subtype _) finset.univ,
          rw finset.mem_map' (function.embedding.subtype _),
          exact finset.mem_univ e₂, },
        refl, }, }, },
end

theorem card_red_colourings_sat_A_R (hk : k ≥ 2) : 
(two_colourings_sat_A_R (complete_graph V) R).card = 
  2 ^ ((fintype.card V).choose 2 - k.choose 2 + 1) := 
begin
  rw all_red_colourings_sat_A_R,
  unfold empty_univ_col_R,
  rw finset.card_map,
  rw finset.card_product,
  rw finset.card_univ,
  rw fintype.card_finset,
  rw fintype.card_coe,
  rw finset.card_sdiff (((complete_graph V).induced_subgraph R).edge_finset_subset),
  rw complete_graph.induced_subgraph.card_edge_finset,
  change (↑R : set V) with (↑(↑R : finset V) : set V),
  simp_rw finset.coe_sort_coe,
  rw fintype.card_coe,
  rw complete_graph.card_edge_finset,
  rw finset.card_doubleton,
  rw pow_succ',
  rw card_R,
  symmetry,
  apply finset.nonempty.ne_empty,
  rw finset.univ_nonempty_iff,
  rw finset.nonempty_coe_sort,
  unfold simple_graph.subgraph.edge_finset,
  rw ← finset.coe_nonempty,
  exact complete_graph.induced_subgraph_size.edge_finset_nonempty R hk,
end

variable (k)

def finset_univ_prod_R_colouring : 
finset (finset.powerset_len k (finset.univ : finset V) ×
  finset ↥G.edge_finset) := finset.univ

theorem finset_univ_prod_R_colouring_eq_prod_univ : 
finset_univ_prod_R_colouring G k = 
  finset.product finset.univ finset.univ :=
begin
  unfold finset_univ_prod_R_colouring,
  exact finset.univ_product_univ,
end

theorem finset_univ_prod_R_colouring_eq_bUnion : 
finset_univ_prod_R_colouring G k = finset.univ.bUnion 
  (λ R, finset.map ⟨prod.mk R, prod.mk.inj_left R⟩ finset.univ) :=
begin
  simp_rw [finset.map_eq_image],
  rw finset_univ_prod_R_colouring_eq_prod_univ,
  exact finset.product_eq_bUnion finset.univ finset.univ,
end

def finset_univ_prod_R_colouring_sat_A_R : 
finset (finset.powerset_len k (finset.univ : finset V) ×
  finset ↥G.edge_finset) :=
finset.filter (λ Rc, A G Rc.fst Rc.snd) (finset_univ_prod_R_colouring G k)

lemma function.uncurry.comp_prod_mk_eq_self 
  {α : Type*} {β : Type*} {γ : Type*} (f : α → β → γ) (a : α) :
(function.uncurry f) ∘ (prod.mk a) = f a := by unfold function.uncurry

theorem finset_univ_prod_R_colouring_sat_A_R_eq_bUnion_filter :
finset_univ_prod_R_colouring_sat_A_R G k = 
  finset.univ.bUnion (λ R, finset.map
    ⟨prod.mk R, prod.mk.inj_left R⟩
    (two_colourings_sat_A_R G R)) :=
begin
  unfold finset_univ_prod_R_colouring_sat_A_R,
  rw finset_univ_prod_R_colouring_eq_bUnion,
  rw finset.filter_bUnion,
  apply congr_arg,
  apply funext,
  intro R,
  unfold two_colourings_sat_A_R,
  rw finset.map_filter,
  apply congr_arg,
  rw function.embedding.coe_fn_mk,
  change (λ Rc : 
      ↥(finset.powerset_len k finset.univ) × finset ↥(G.edge_finset),
    A G Rc.fst Rc.snd) with function.uncurry (A G),
  simp_rw [function.uncurry.comp_prod_mk_eq_self],
  unfold finset_univ_two_colouring,
end

theorem card_finset_univ_prod_R_colouring_sat_A_R {k} (hk : k ≥ 2) :
(finset_univ_prod_R_colouring_sat_A_R (complete_graph V) k).card = 
  (fintype.card V).choose k * 2 ^ ((fintype.card V).choose 2 -
    k.choose 2 + 1) :=
begin
  rw finset_univ_prod_R_colouring_sat_A_R_eq_bUnion_filter,
  rw finset.card_bUnion,
  rw finset.sum_const_nat,
  swap 3,
  { exact 2 ^ ((fintype.card V).choose 2 - k.choose 2 + 1) },
  { rw finset.card_univ,
    rw fintype.card_coe,
    rw finset.card_powerset_len,
    rw finset.card_univ, },
  { intros R R_in,
    rw finset.card_map,
    rw card_red_colourings_sat_A_R,
    exact hk, },
  intros R R_in R' R'_in R_ne_R',
  rw finset.disjoint_iff_ne,
  rintros ⟨R₁, c⟩ Rc_in ⟨R'₁, c'⟩ R'c'_in,
  simp only [finset.mem_map, function.embedding.coe_fn_mk,
    prod.mk.inj_iff, exists_prop, exists_eq_right_right] at Rc_in R'c'_in,
  rw ← Rc_in.right,
  rw ← R'c'_in.right,
  rw ne.def,
  rw prod.mk.inj_iff,
  exact not_and_of_not_left _ R_ne_R',
end

def finset_univ_colouring_sat_A : finset (finset ↥G.edge_finset) := 
finset.image prod.snd (@finset_univ_prod_R_colouring_sat_A_R _ _ _ G _ k)

theorem finset_univ_prod_R_colouring_sat_A_R_ssubset_univ {k} 
( h : ((fintype.card V).choose k) * 2 ^ 
    ((fintype.card V).choose 2 - k.choose 2 + 1) <
    2 ^ (fintype.card V).choose 2) (hk : k ≥ 2) : 
finset_univ_colouring_sat_A (complete_graph V) k ⊂ 
  (finset_univ_two_colouring (complete_graph V)) :=
begin
  unfold finset_univ_two_colouring,
  rw finset.ssubset_iff_subset_ne,
  split,
  { exact finset.subset_univ _, },
  { rw ← finset.card_lt_iff_ne_univ,
    calc (finset_univ_colouring_sat_A (complete_graph V) k).card ≤
      (finset_univ_prod_R_colouring_sat_A_R (complete_graph V) k).card :
        finset.card_image_le
      ... = (fintype.card V).choose k * 2 ^ 
            ((fintype.card V).choose 2 - k.choose 2 + 1) : 
        card_finset_univ_prod_R_colouring_sat_A_R hk
      ... < 2 ^ (fintype.card V).choose 2 : h
      ... = finset.univ.card : 
        begin 
          rw finset.card_univ, 
          rw fintype.card_finset, 
          rw fintype.card_coe, 
          rw complete_graph.card_edge_finset
        end, },
end

theorem ramsey_lower_bound {k} 
( h : ((fintype.card V).choose k) * 2 ^
    ((fintype.card V).choose 2 - k.choose 2 + 1) < 
    2 ^ (fintype.card V).choose 2) (hk : k ≥ 2) :
∃ c : finset ↥((complete_graph V).edge_finset),
  ¬∃ R' : ↥(finset.powerset_len k (finset.univ : finset V)),
    A (complete_graph V) R' c :=
begin
  rcases 
    finset.exists_of_ssubset 
      (finset_univ_prod_R_colouring_sat_A_R_ssubset_univ h hk) 
    with ⟨c, c_in, c_not_in⟩,
  use c,
  convert_to ¬∃ R', 
    (R', c) ∈ (finset_univ_prod_R_colouring_sat_A_R (complete_graph V) k),
  { unfold finset_univ_prod_R_colouring_sat_A_R,
    simp_rw finset.mem_filter,
    unfold finset_univ_prod_R_colouring,
    simp_rw [eq_true_intro (finset.mem_univ _)],
    simp_rw [true_and], },
  unfold finset_univ_colouring_sat_A at c_not_in,
  rw finset.mem_image at c_not_in,
  rw not_exists at c_not_in,
  rw not_exists,
  intro R,
  specialize c_not_in (R, c),
  rw not_exists at c_not_in,
  rw eq_self_iff_true at c_not_in,
  rw not_true at c_not_in,
  rw imp_false at c_not_in,
  exact c_not_in,
end