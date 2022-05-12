import data.finset.basic
import data.fintype.basic

namespace subset_subtype

variable {α : Type*}
variable {t : finset α}
variable t' : {s // s ⊆ t}

namespace finset_subtype

def coe : finset ↥t :=
finset.map 
  ⟨set.inclusion t'.property, set.inclusion_injective t'.property⟩ 
  (finset.univ : finset ↥(t'.val))

instance has_coe : 
  has_coe ({s // s ⊆ t}) (finset ↥t) := ⟨coe⟩

theorem coe_injective :
function.injective (coe : {s // s ⊆ t} → (finset ↥t)) :=
begin
  unfold function.injective,
  intros s₁ s₂ h,
  unfold coe at h,
  rw subtype.ext_iff,
  rw finset.ext_iff,
  intro x,
  split,
  { intro x_in₁,
    rw finset.ext_iff at h,
    specialize h ⟨x, finset.mem_of_subset s₁.property x_in₁⟩,
    change (⟨x, finset.mem_of_subset s₁.property x_in₁⟩ : ↥t) with
      (⟨set.inclusion s₁.property,
        set.inclusion_injective s₁.property ⟩ : function.embedding _ _)
        ⟨x, x_in₁⟩ at h,
    rw finset.mem_map' at h,
    have x_in₂ := h.mp (finset.mem_univ ⟨x, x_in₁⟩),
    rw finset.mem_map at x_in₂,
    rcases x_in₂ with ⟨x', _, h'⟩,
    change (⟨x'.val, _⟩ : ↥t) = ⟨x, _⟩ at h',
    rw subtype.mk_eq_mk at h',
    have x'_in₂ := x'.property,
    rw h' at x'_in₂,
    exact x'_in₂, },
  { intro x_in₂,
    rw finset.ext_iff at h,
    specialize h ⟨x, finset.mem_of_subset s₂.property x_in₂⟩,
    change (⟨x, finset.mem_of_subset s₂.property x_in₂⟩ : ↥t) with
      (⟨set.inclusion s₂.property, 
        set.inclusion_injective s₂.property ⟩ : function.embedding _ _) 
        ⟨x, x_in₂⟩ at h,
    rw finset.mem_map' at h,
    have x_in₁ := h.mpr (finset.mem_univ ⟨x, x_in₂⟩),
    rw finset.mem_map at x_in₁,
    rcases x_in₁ with ⟨x', _, h'⟩,
    change (⟨x'.val, _⟩ : ↥t) = ⟨x, _⟩ at h',
    rw subtype.mk_eq_mk at h',
    have x'_in₁ := x'.property,
    rw h' at x'_in₁,
    exact x'_in₁, },
end

end finset_subtype

lemma coe_type : finset.map 
  (function.embedding.subtype (∈ t)) 
  (finset_subtype.coe t') = t'.val :=
begin
  rw finset.ext_iff,
  intro x,
  unfold finset_subtype.coe,
  rw finset.mem_map,
  simp only [ subtype.val_eq_coe, finset.mem_map, finset.mem_univ,
              function.embedding.coe_fn_mk, set_coe.exists,
              function.embedding.coe_subtype, exists_prop, subtype.exists,
              subtype.coe_mk, exists_and_distrib_right, exists_eq_right,
              true_and ],
  split,
  { rintro ⟨x_in_t, x', x'_in_s, h'⟩,
    change (⟨x', _⟩ : ↥t) = ⟨x, _⟩ at h',
    rw subtype.mk_eq_mk at h',
    rw ← h',
    exact x'_in_s, },
  { intro x_in_s,
    use finset.mem_of_subset t'.property x_in_s,
    use x,
    use x_in_s,
    refl, },
end 

end subset_subtype