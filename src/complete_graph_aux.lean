import combinatorics.simple_graph.basic
import combinatorics.simple_graph.subgraph
import simple_graph_aux
import finset_fintype_aux

namespace complete_graph

open simple_graph

universe u

variables {V : Type u} [fintype V] [decidable_eq V]  
variable (G : simple_graph V)

lemma edge_to_finset_powerset_len_two_surj : 
∀ s, ∃ e, ∃ e_in, 
  (complete_graph V).edge_to_finset_powerset_len_two e e_in = s :=
begin
  rintro ⟨s, s_in⟩,
  rw finset.mem_powerset_len at s_in,
  cases s_in with s_subset card_s,
  rw finset.card_eq_two at card_s,
  rcases card_s with ⟨v₁, v₂, v₁_ne_v₂, hs⟩,
  use ⟦(v₁, v₂)⟧,
  simp only [mem_edge_set, complete_graph_eq_top, top_adj],
  use v₁_ne_v₂,
  unfold edge_to_finset_powerset_len_two,
  simp only [sym2.lift_mk, subtype.coe_mk, subtype.mk_eq_mk],
  exact hs.symm,
end

lemma card_edge_finset : 
(complete_graph V).edge_finset.card = (fintype.card V).choose 2 :=
begin
  suffices : (complete_graph V).edge_finset.card = 
    (finset.powerset_len 2 (finset.univ : finset V)).card,
  { rw this,
    exact finset.card_powerset_len _ _, },
  unfold simple_graph.edge_finset,
  refine finset.card_congr 
    (λ e, λ e_in, 
      ((complete_graph V).edge_to_finset_powerset_len_two 
        e (by rwa ← set.mem_to_finset)).val) _ _ _,
  { simp only [subtype.val_eq_coe, finset.coe_mem, implies_true_iff], },
  { simp_rw set.mem_to_finset,
    simp_rw subtype.val_inj,
    exact (complete_graph V).edge_to_finset_powerset_len_two_inj, },
  { intros s s_in,
    have h_surj := edge_to_finset_powerset_len_two_surj ⟨s, s_in⟩,
    simp_rw ← subtype.val_inj at h_surj,
    simp_rw set.mem_to_finset,
    exact h_surj, },
end

theorem edge_set_nonempty (hV : fintype.card V ≥ 2) : 
((complete_graph V).edge_set).nonempty :=
begin
  unfold set.nonempty,
  unfold simple_graph.edge_set,
  rcases fintype.ex_x_ne_y_of_card_ge_two hV with ⟨v₁, v₂, v₁_ne_v₂⟩,
  use ⟦(v₁, v₂)⟧, 
  -- Lean infers that ⟦(x, y)⟧ is an edge using hxy and closes the goal early
end

theorem edge_finset_nonempty (hV : fintype.card V ≥ 2) :
((complete_graph V).edge_finset).nonempty :=
begin
  unfold edge_finset,
  rw ← finset.coe_nonempty,
  rw set.coe_to_finset,
  exact edge_set_nonempty hV,
end

end complete_graph