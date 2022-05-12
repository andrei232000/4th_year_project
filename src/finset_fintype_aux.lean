import data.finset.basic
import data.fintype.basic

namespace finset

theorem ex_x_ne_y_of_card_ge_two {α : Type*} [decidable_eq α] 
  {s : finset α} : s.card ≥ 2 → ∃ x ∈ s, ∃ y ∈ s, x ≠ y :=
begin
  intro h_card,
  have hs : ∃ n : ℕ, s.card = n + 2,
  { use s.card - 2,
    rw ← nat.sub_eq_iff_eq_add,
    exact h_card, },
  cases hs with n hn,
  rw finset.card_eq_succ at hn,
  rcases hn with ⟨x, s', hx, hs', hn'⟩, 
  rw finset.card_eq_succ at hn',
  rcases hn' with ⟨y, s'', _, hs'', _⟩,
  have hy : y ∈ s',
  { rw ← hs'',
    exact finset.mem_insert_self y s'', },
  use x,
  split,
  { rw ← hs',
    exact finset.mem_insert_self x s', },
  { use y,
    split,
    apply finset.mem_of_subset,
    { rw ← hs',
      exact finset.subset_insert x s', },
    { exact hy, },
    symmetry,
    exact ne_of_mem_of_not_mem hy hx, },
end

end finset

namespace fintype

theorem ex_x_ne_y_of_card_ge_two {α : Type*} 
  [decidable_eq α] [fintype α] : 
fintype.card α ≥ 2 → ∃ x y : α, x ≠ y :=
begin
  intro h_card,
  rcases finset.ex_x_ne_y_of_card_ge_two 
    (show finset.univ.card ≥ 2, by {rw finset.card_univ, exact h_card})
    with ⟨x, _, y, _, hxy⟩,
  exact ⟨x, y, hxy⟩,
end

end fintype