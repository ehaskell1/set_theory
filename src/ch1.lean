import logic
import set_theory.zfc

namespace Set

-- We have ext axiom. (Set.ext)
-- Set.eq_empty proves there is only one empty set (using extensionality).
-- We have pairing axiom. (Set.mem_pair)
theorem pair_commutative {x y : Set} : ({x, y} : Set) = {y, x} :=
begin
  apply Set.ext,
  intro z,
  simp [Set.mem_pair] at *,
  exact or.comm,
end
theorem singleton_of_pair_self {x : Set} : ({x, x} : Set) = {x} :=
begin
  apply Set.ext,
  intro z,
  simp [Set.mem_pair] at *,
end
def from_list : list Set → Set
| [] := ∅
| (hd :: tl) := {hd} ∪ from_list tl
theorem mem_from_list {l : list Set} (z : Set) : z ∈ from_list l ↔ z ∈ l :=
begin
  induction l with hd tl ih,
    simp only [list.mem_nil_iff, iff_false, from_list], exact Set.mem_empty _,
  simp only [from_list, list.mem_cons_iff, Set.mem_union, Set.mem_singleton],
  rw ih,
end
theorem empty_is_subset (x : Set) : ∅ ⊆ x :=
begin
  intros z h,
  exfalso, exact (Set.mem_empty _) h,
end
theorem p2a : (∅ : Set) ≠ {∅} :=
begin
  intro he,
  have h : ∅ ∈ {∅} := Set.mem_singleton.mpr rfl,
  rw ←he at h,
  exact Set.mem_empty _ h,
end
theorem p2b : ({∅} : Set) ≠ {{∅}} :=
begin
  intro he,
  have h : {∅} ∈ {{∅}} := Set.mem_singleton.mpr rfl,
  rw ←he at h,
  rw Set.mem_singleton at h,
  exact p2a h.symm,
end
theorem p2c : (∅ : Set) ≠ {{∅}} :=
begin
  intro he,
  have h : {∅} ∈ {{∅}} := Set.mem_singleton.mpr rfl,
  rw ←he at h,
  exact Set.mem_empty _ h,
end
-- powerset axiom enabled by Set.powerset and Set.mem_powerset
theorem p4 {x y B : Set} (h : {x, y} ⊆ B) : x.pair y ∈ B.powerset.powerset :=
begin
  simp only [Set.mem_powerset, Set.pair],
  intros z hm,
  simp only [Set.mem_pair] at hm,
  simp only [Set.mem_powerset],
  cases hm,
  { rw hm,
    intros s he,
    rw Set.mem_singleton at he,
    rw he,
    apply h,
    simp only [Set.mem_pair],
    left, refl, },
  { rw hm,
    exact h, },
end
def finite_hierarchy : ℕ → Set
| 0 := ∅
| (n + 1) := let V := finite_hierarchy n in V ∪ V.powerset
theorem subset_union_of_subset {x y z : Set} (h : x ⊆ z) : x ⊆ z ∪ y :=
begin
  intros c hm,
  specialize h hm,
  simp only [Set.mem_union],
  left, exact h,
end
theorem subset_finite_hierarchy_of_mem {n : ℕ} {x : Set} : x ∈ finite_hierarchy n → x ⊆ finite_hierarchy n :=
begin
  induction n with m ih,
  { simp only [finite_hierarchy],
    intro h,
    exfalso,
    exact Set.mem_empty _ h, },
  { simp only [finite_hierarchy, Set.mem_union],
    intros h,
    cases h,
    exact subset_union_of_subset (ih h),
    exact subset_union_of_subset (Set.mem_powerset.mp h), },
end
theorem finite_hierarchy_succ (n : ℕ) : finite_hierarchy (n + 1) = (finite_hierarchy n).powerset :=
begin
  simp only [finite_hierarchy],
  apply Set.ext,
  simp only [Set.mem_union],
  intro z,
  split; intro h,
  { cases h,
      simp only [Set.mem_powerset],
      exact subset_finite_hierarchy_of_mem h,
    exact h, },
  { right, exact h, },
end

lemma singleton_eq {x y : Set} : ({x} : Set) = {y} ↔ x = y :=
begin
  rw ←Set.ext_iff, simp only [Set.mem_singleton], exact eq_iff_eq_cancel_left, 
end

end Set