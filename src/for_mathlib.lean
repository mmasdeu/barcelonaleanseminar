import data.real.basic
import data.real.ereal
import order.conditionally_complete_lattice

open set
open_locale classical
noncomputable theory

@[simp]
lemma set.eq_univ_iff_forall' {α : Type} (p : α → Prop) : {x : α | p x} = univ ↔ ∀ x, p x :=
set.eq_univ_iff_forall

@[simp]
lemma set.eq_empty_iff_forall_not_mem' {α : Type} {p : α → Prop} : {x : α | p x} = ∅ ↔ ∀ x, ¬ p x :=
set.eq_empty_iff_forall_not_mem

lemma sUnion_eq_of_pointwise {X : Type} {U : set X} {ℬ : set (set X)} :
  ( ∃ J ⊆ ℬ, U = ⋃₀ J ) ↔  (∀ x ∈ U, ∃ W ∈ ℬ, x ∈ W ∧ W ⊆ U) :=
begin
  split,
  { rintros ⟨J, hJ1, rfl⟩ x ⟨t, ht1, ht2⟩,
    exact ⟨t, hJ1 ht1, ht2, subset_sUnion_of_mem ht1⟩ },
  { intro h,
    refine ⟨{W ∈ ℬ | W ⊆ U}, sep_subset _ _, _⟩,
    apply eq_of_subset_of_subset,
    { intros x hx,
      obtain ⟨W, hWB, hXw, hwu⟩ := h x hx,
      exact ⟨W, ⟨hWB, hwu⟩, hXw⟩ },
    { rintros x ⟨W, ⟨-, hWU⟩, hXw⟩,
      exact hWU hXw, } }
end

lemma ereal.eq_top_iff (x : ereal) : x = ⊤ ↔ ∀ (y : ℝ), (y : ereal) < x :=
begin
  split,
  { intro h,
    subst h,
    exact ereal.coe_lt_top },
  { intro h,
    by_contradiction hc,
    by_cases hb : x = ⊥,
    { subst hb,
      simpa [not_lt_bot] using (h 0) },
    let z := x.to_real,
    have hz : (z : ereal) = x := ereal.coe_to_real hc hb,
    simpa [hz] using (h z) }
end

lemma ereal.eq_bot_iff (x : ereal) : x = ⊥ ↔ ∀ (y : ℝ), x < (y : ereal) :=
begin
  split,
  { intro h,
    subst h,
    exact ereal.bot_lt_coe },
  { intro h,
    by_contradiction hc,
    by_cases ht : x = ⊤,
    { subst ht,
      simpa [not_lt_bot] using (h 0) },
    let z := x.to_real,
    have hz : (z : ereal) = x := (ereal.coe_to_real ht hc),
    simpa [hz] using (h z) }
end

lemma inter_is_not_is_empty_intersection {X : Type} {x : X} {U V : set X}
  (hxU : x ∈ U) (hUV : U ∩ V = ∅ ) : x ∉ V := disjoint_left.1 (disjoint_iff_inter_eq_empty.2 hUV) hxU

lemma image_sUnion {X Y: Type} (A: set(set X)) (f: X → Y) : f '' (⋃₀ A) = ⋃₀ { V: set Y | ∃ U: set X, U ∈ A ∧ V = f '' U}:=
begin
  ext1 y,
  split,{
    rintro ⟨x, ⟨U, hU, hx⟩, _⟩,
    use f '' U,
    simp only [mem_image, mem_set_of_eq],
    tauto,
  },
  {
    rintro ⟨_, ⟨⟨U, hU, _, _⟩, x, _⟩⟩,
    use x,
    simp only [exists_prop, mem_set_of_eq],
    tauto,
  },
end

lemma neq_elements_prod {X Y : Type} {x y : X × Y} (h : x ≠ y) : x.1 ≠ y.1 ∨ x.2 ≠ y.2 :=
begin
  by_contradiction hh,
  push_neg at hh,
  exact h (prod.ext_iff.mpr hh),
end

lemma abs_add_nonneg (x : ℝ) : 0 ≤ abs x + x :=
begin
  by_cases h : 0 ≤ x,
  { linarith [abs_of_nonneg h] },
  { push_neg at h,
    linarith [abs_of_neg h] },
end
