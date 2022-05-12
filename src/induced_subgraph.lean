import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import data.finset.basic
import data.finset.powerset
import data.fintype.basic
import logic.basic
import simple_graph_aux
import finset_fintype_aux

universe u

variable {V : Type u}

variable G : simple_graph V
variable R : set V
variables R₁ R₂ : set V

namespace simple_graph

def induced_subgraph : G.subgraph :=
{ verts := R,
  adj := λ v w, v ∈ R ∧ w ∈ R ∧ G.adj v w,
  adj_sub := λ _ _ ⟨_, _, G_adj⟩, G_adj,
  edge_vert := λ _ _ ⟨v_in,_ , _⟩, v_in, }

lemma induced_subgraph_adj_eq_of_verts_eq :
  (induced_subgraph G R₁).verts = (induced_subgraph G R₂).verts →
    (induced_subgraph G R₁).adj = (induced_subgraph G R₂).adj :=
begin
  intro h_verts,
  change R₁ = R₂ at h_verts,
  rw h_verts,
end

lemma induced_subgraph_injective : function.injective (induced_subgraph G) :=
begin
  unfold function.injective,
  intros R₁ R₂,
  rw subgraph.ext_iff,
  rintro ⟨h_verts, _⟩,
  exact h_verts,
end

namespace induced_subgraph_size

variable (k : ℕ)

def set_univ : set G.subgraph := set.image
  (induced_subgraph G) 
  {Rₖ : set V | ∃ fin_Rₖ : fintype ↥Rₖ, (@set.to_finset _ Rₖ (by assumption)).card = k}

section finite

variable [fintype V]

def finset_univ : finset G.subgraph := finset.map
⟨ (induced_subgraph G) ∘ coe,
  function.injective.comp (induced_subgraph_injective G) finset.coe_injective ⟩
  (finset.powerset_len k (finset.univ : finset V))

lemma set_univ_eq_coe : (set_univ G k) = ↑(finset_univ G k) :=
begin
  apply set.ext,
  intro G',
  rw finset.mem_coe,
  unfold set_univ,
  unfold finset_univ,
  rw set.mem_image,
  rw finset.mem_map,
  split,
  { rintro ⟨Rₖ, h_Rₖ, h_G'⟩,
    rw set.mem_set_of_eq at h_Rₖ,
    cases h_Rₖ with fin_Rₖ card_Rₖ,
    use @set.to_finset _ Rₖ (by assumption),
    split,
    { rw finset.mem_powerset_len,
      exact ⟨finset.subset_univ _, card_Rₖ⟩, },
    { rw function.embedding.coe_fn_mk,
      rw function.comp_app,
      rw set.coe_to_finset,
      exact h_G', }, },
  { rintro ⟨Rₖ, Rₖ_in, h_G'⟩,
    rw function.embedding.coe_fn_mk at h_G',
    use ↑Rₖ,
    split,
    { rw set.mem_set_of_eq,
      use (finset_coe.fintype Rₖ),
      rw set.to_finset_card,
      simp_rw [finset.coe_sort_coe],
      rw fintype.card_coe,
      rw finset.mem_powerset_len at Rₖ_in,
      exact Rₖ_in.right, },
    { rw function.comp_app at h_G',
      exact h_G', }, },
end

lemma card_set_univ :
(finset_univ G k).card = (fintype.card V).choose k := 
begin
  unfold finset_univ,
  rw finset.card_map,
  rw finset.card_powerset_len,
  rw finset.card_univ,
end

end finite

end induced_subgraph_size

namespace induced_subgraph

lemma is_induced : subgraph.is_induced (induced_subgraph G R) :=
begin
  unfold subgraph.is_induced,
  unfold induced_subgraph,
  dsimp [induced_subgraph],
  intros v w v_in w_in G_adj,
  exact ⟨v_in, w_in, G_adj⟩,
end

namespace decidable

variable [decidable_eq V]
variable [decidable_rel G.adj]
variable [decidable_pred (∈ R)]

instance adj : decidable_rel (G.induced_subgraph R).adj :=
begin
  unfold decidable_rel,
  intros v w,
  unfold induced_subgraph,
  simp only [],
  apply_instance,
end

instance coe_adj : decidable_rel (G.induced_subgraph R).coe.adj :=
begin
  unfold decidable_rel,
  intros v w,
  unfold subgraph.coe,
  simp only [],
  apply_instance,
end

instance verts_mem : decidable_pred (∈ (G.induced_subgraph R).verts) :=
begin
  unfold induced_subgraph,
  simp only [],
  apply_instance,
end

end decidable

section finite

variables [fintype V]
variables [decidable_pred (∈ R)]

instance verts_fintype : fintype ↥(induced_subgraph G R).verts :=
begin
  unfold induced_subgraph,
  change fintype ↥R,
  apply_instance,
end

variable [decidable_eq V]
variable [decidable_rel G.adj]

def edge_subtype_finset (s : finset (sym2 V)) :
finset ↥((G.induced_subgraph R).edge_finset) :=
finset.subtype _ s

def edge_complement_subtype_finset (s : finset (sym2 V)) :
finset ↥(G.edge_finset \ (G.induced_subgraph R).edge_finset) :=
finset.subtype _ s

end finite

end induced_subgraph

end simple_graph

namespace complete_graph

open simple_graph

namespace induced_subgraph

lemma coe_eq_complete_graph : ((complete_graph V).induced_subgraph R).coe = complete_graph ↥R :=
begin
  rw simple_graph.ext_iff,
  funext,
  rw subgraph.coe_adj,
  unfold induced_subgraph,
  simp only [],
  ext,
  change ↥R at v,
  change ↥R at w,
  rw ← subtype.val_eq_coe,
  rw ← subtype.val_eq_coe,
  rw eq_true_intro v.property,
  rw eq_true_intro w.property,
  rw true_and,
  rw true_and,
  unfold complete_graph,
  simp only [],
  rw ne.def,
  rw subtype.val_inj,
end

section finite

variables [decidable_eq V] [fintype V] [decidable_pred (∈ R)]

def edge_to_finset_powerset_len_two_surj  : 
∀ s,
  ∃ e, ∃ e_in,
    ((complete_graph V).induced_subgraph R).edge_to_finset_powerset_len_two e e_in = s :=
begin
  rintro ⟨s, s_in⟩,
  rw finset.mem_powerset_len at s_in,
  cases s_in with s_subset card_s,
  rw finset.card_eq_two at card_s,
  rcases card_s with ⟨v₁, v₂, v₁_ne_v₂, hs⟩,
  use ⟦(v₁, v₂)⟧,
  unfold induced_subgraph,
  simp only [subgraph.mem_edge_set, complete_graph_eq_top, top_adj],
  unfold induced_subgraph at s_subset,
  change s ⊆ R.to_finset at s_subset,
  have v₁_in : v₁ ∈ R,
  { rw ← set.mem_to_finset,
    apply finset.mem_of_subset s_subset,
    rw hs,
    simp only [finset.mem_insert, eq_self_iff_true, true_or], },
  have v₂_in : v₂ ∈ R,
  { rw ← set.mem_to_finset,
    apply finset.mem_of_subset s_subset,
    rw hs,
    simp only [finset.mem_insert, finset.mem_singleton, eq_self_iff_true, or_true], },
  use ⟨v₁_in, v₂_in, v₁_ne_v₂⟩,
  unfold subgraph.edge_to_finset_powerset_len_two,
  simp only [sym2.lift_mk, subtype.coe_mk, subtype.mk_eq_mk],
  exact hs.symm,
end

lemma card_edge_finset : ((complete_graph V).induced_subgraph R).edge_finset.card = (fintype.card ↥R).choose 2 :=
begin
  suffices : (((complete_graph V).induced_subgraph R).edge_finset).card = (finset.powerset_len 2 R.to_finset).card,
  { rw this,
    rw ← set.to_finset_card R,
    exact finset.card_powerset_len _ _, },
  unfold subgraph.edge_finset,
  refine finset.card_congr 
    (λ e, λ e_in, 
      (((complete_graph V).induced_subgraph R).edge_to_finset_powerset_len_two 
        e (by rwa ← set.mem_to_finset)).val) _ _ _,
  { intros e e_in,
    rw subtype.val_eq_coe,
    have h := (((complete_graph V).induced_subgraph R).edge_to_finset_powerset_len_two e _).prop,
    unfold induced_subgraph at h,
    exact h, },
  { simp_rw set.mem_to_finset,
    simp_rw subtype.val_inj,
    exact ((complete_graph V).induced_subgraph R).edge_to_finset_powerset_len_two_inj, },
  { intros s s_in,
    have h_surj := edge_to_finset_powerset_len_two_surj R 
      ⟨s, by {unfold induced_subgraph, exact s_in}⟩,
    simp_rw ← subtype.val_inj at h_surj,
    simp_rw set.mem_to_finset,
    exact h_surj },
end

end finite

end induced_subgraph

namespace induced_subgraph_size

variables [fintype V] [decidable_eq V]
variable {k : ℕ}
variable Rₖ : ↥(finset.powerset_len k (finset.univ : finset V))

lemma card_Rₖ : (Rₖ : finset V).card = k :=
begin
  cases Rₖ with Rₖ Rₖ_in,
  change Rₖ.card = k,
  rw finset.mem_powerset_len at Rₖ_in,
  rw Rₖ_in.right,
end

instance Rₖ_mem_decidable : decidable_pred (∈ (↑Rₖ : set V)) := 
λ a, finset.decidable_mem a Rₖ

theorem edge_set_nonempty (hk : k ≥ 2) :
(((complete_graph V).induced_subgraph Rₖ).edge_set).nonempty :=
begin
  unfold set.nonempty,
  unfold subgraph.edge_set,
  rw sym2.exists,
  simp_rw [sym2.from_rel_prop],
  unfold induced_subgraph,
  change ∃ (v₁ v₂ : V),
    v₁ ∈ ↑Rₖ ∧ v₂ ∈ ↑Rₖ ∧ (complete_graph V).adj v₁ v₂,
  unfold complete_graph,
  simp only [],
  have hRₖ_card : (Rₖ : finset V).card ≥ 2,
  { rw card_Rₖ,
    exact hk, },
  rcases finset.ex_x_ne_y_of_card_ge_two hRₖ_card with 
    ⟨v₁, v₁_in, v₂, v₂_in, v₁_ne_v₂⟩,
  exact ⟨v₁, v₂, v₁_in, v₂_in, v₁_ne_v₂⟩,
end

theorem edge_finset_nonempty (hk : k ≥ 2) :
(((complete_graph V).induced_subgraph Rₖ).edge_finset).nonempty :=
begin
  unfold subgraph.edge_finset,
  rw ← finset.coe_nonempty,
  rw set.coe_to_finset,
  exact edge_set_nonempty Rₖ hk,
end

end induced_subgraph_size

end complete_graph