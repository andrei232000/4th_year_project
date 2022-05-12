import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph

namespace simple_graph

universe u

variables {V : Type u} [fintype V] [decidable_eq V]
variable (G : simple_graph V)

def edge_to_finset_powerset_len_two : Π (e : sym2 V), 
  e ∈ G.edge_set → ↥(finset.powerset_len 2 (finset.univ : finset V)) :=
λ e, λ e_in, 
⟨ sym2.lift ⟨λ v₁ v₂ : V, ({v₁, v₂} : finset V), 
    λ v₁ v₂ : V, finset.insert.comm v₁ v₂ ∅⟩ e,
  begin
    revert e,
    rw sym2.forall,
    unfold simple_graph.edge_set,
    intros v₁ v₂,
    rw sym2.from_rel_prop,
    intro h_adj,
    simp only [sym2.lift_mk, subtype.coe_mk],
    rw finset.mem_powerset_len,
    rw finset.card_eq_two,
    have v₁_ne_v₂ : v₁ ≠ v₂,
    { intro x_eq_y,
      rw x_eq_y at h_adj,
      exact G.loopless v₂ h_adj, },
    exact ⟨finset.subset_univ {v₁, v₂}, ⟨v₁, v₂, v₁_ne_v₂, rfl⟩⟩,
  end ⟩

lemma edge_to_finset_powerset_len_two_inj : ∀ e₁ e₂ e₁_in e₂_in,
  G.edge_to_finset_powerset_len_two e₁ e₁_in = 
    G.edge_to_finset_powerset_len_two e₂ e₂_in → 
  e₁ = e₂ :=
begin
  rw sym2.forall,
  intros v₁ v₂,
  rw sym2.forall,
  intros v₁' v₂',
  intros e₁_in e₂_in h_eq,
  apply sym2.ext,
  rw ← subtype.val_inj at h_eq,
  unfold edge_to_finset_powerset_len_two at h_eq,
  simp only [sym2.lift_mk, subtype.coe_mk] at h_eq,
  rw finset.ext_iff at h_eq,
  simp only [finset.mem_insert, finset.mem_singleton] at h_eq,
  simp_rw sym2.mem_iff,
  exact h_eq,
end

namespace subgraph

variables {G} [decidable_rel G.adj]
variables (G' : G.subgraph) [decidable_rel G'.adj]

namespace decidable

instance edge_set_mem :
decidable_pred (∈ G'.edge_set) := sym2.from_rel.decidable_pred G'.symm

instance coe_adj : decidable_rel G'.coe.adj := 
begin
  unfold decidable_rel,
  intros v w,
  rw simple_graph.subgraph.coe_adj,
  apply_instance,
end

instance coe_edge_set_mem [decidable_pred (∈ G'.verts)] :
decidable_pred (∈ G'.coe.edge_set) :=
sym2.from_rel.decidable_pred G'.coe.symm

end decidable

def edge_finset : finset (sym2 V) := G'.edge_set.to_finset

lemma edge_finset_subset : G'.edge_finset ⊆ G.edge_finset := 
begin
  unfold edge_finset,
  unfold simple_graph.edge_finset,
  rw ← set.subset_iff_to_finset_subset,
  exact G'.edge_set_subset,
end

def edge_to_finset_powerset_len_two [decidable_pred (∈ G'.verts)] : Π (e : sym2 V), 
  e ∈ G'.edge_set → ↥(finset.powerset_len 2 G'.verts.to_finset) :=
λ e, λ e_in,
⟨ sym2.lift ⟨λ v₁ v₂ : V, ({v₁, v₂} : finset V), 
    λ v₁ v₂ : V, finset.insert.comm v₁ v₂ ∅⟩ e,
  begin
    revert e,
    rw sym2.forall,
    unfold simple_graph.subgraph.edge_set,
    intros v₁ v₂,
    rw sym2.from_rel_prop,
    intro h_adj,
    simp only [sym2.lift_mk, subtype.coe_mk],
    rw finset.mem_powerset_len,
    rw finset.card_eq_two,
    have v₁_ne_v₂ : v₁ ≠ v₂,
    { intro v₁_eq_v₂,
      rw v₁_eq_v₂ at h_adj,
      exact G'.loopless v₂ h_adj, },
    have h_subset : {v₁, v₂} ⊆ G'.verts.to_finset,
    { rw finset.subset_iff,
      simp only [finset.mem_insert, finset.mem_singleton, set.mem_to_finset, forall_eq_or_imp, forall_eq],
      exact ⟨G'.edge_vert h_adj, G'.edge_vert (G'.symm h_adj)⟩, },
    exact ⟨h_subset, ⟨v₁, v₂, v₁_ne_v₂, rfl⟩⟩,
  end ⟩

def edge_to_finset_powerset_len_two_inj [decidable_pred (∈ G'.verts)] : ∀ e₁ e₂ e₁_in e₂_in,
  G'.edge_to_finset_powerset_len_two e₁ e₁_in = 
    G'.edge_to_finset_powerset_len_two e₂ e₂_in → 
  e₁ = e₂ :=
begin
  rw sym2.forall,
  intros v₁ v₂,
  rw sym2.forall,
  intros v₁' v₂',
  intros e₁_in e₂_in h_eq,
  apply sym2.ext,
  rw ← subtype.val_inj at h_eq,
  unfold edge_to_finset_powerset_len_two at h_eq,
  simp only [sym2.lift_mk, subtype.coe_mk] at h_eq,
  rw finset.ext_iff at h_eq,
  simp only [finset.mem_insert, finset.mem_singleton] at h_eq,
  simp_rw sym2.mem_iff,
  exact h_eq,
end

end subgraph

end simple_graph