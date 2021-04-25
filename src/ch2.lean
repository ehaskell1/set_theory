import ch1

namespace Set

theorem russels_paradox : ¬ ∃ S : Set, ∀ x, x ∈ S ↔ x ∉ x :=
begin
  rintro ⟨S, hs⟩,
  specialize hs S,
  exact (iff_not_self _).mp hs,
end
-- axiom of specification is enabled by has_sep and mem_sep
theorem univ_not_set : ¬ ∃ S : Set, ∀ x, x ∈ S :=
begin
  rintro ⟨S, hs⟩,
  apply russels_paradox,
  let B := {x ∈ S | x ∉ x},
  refine ⟨B, _⟩,
  intro x,
  rw mem_sep,
  exact and_iff_right (hs x),
end
theorem univ_not_set' (A : Set) : ∃ x, x ∉ A :=
begin
  let B := {x ∈ A | x ∉ x},
  refine ⟨B, _⟩,
  intro he,
  suffices h : B ∈ B ↔ B ∈ A ∧ B ∉ B,
    rw @and_iff_right _ (B ∉ B) he at h,
    exact (iff_not_self (B ∈ B)).mp h,
  exact mem_sep,
end
-- set union enabled by Union and mem_Union
theorem union_empty_eq_empty : (∅ : Set).Union = ∅ :=
begin
  apply ext, intro z,
  rw (iff_false _).mpr (mem_empty z),
  rw iff_false,
  rw mem_Union,
  rintro ⟨y, H, hi⟩,
  exact mem_empty y H,
end
def Inter (A : Set) : Set := {x ∈ A.Union | ∀ z ∈ A, x ∈ z}
def inhab (A : Set) : Prop := ∃ x, x ∈ A
theorem ne_empty_of_inhabited (A : Set) (h : A.inhab) : A ≠ ∅ :=
begin
  cases h with x h,
  intro he,
  rw he at h,
  exact mem_empty x h,
end
theorem inhabited_of_ne_empty {A : Set} (hA : A ≠ ∅) : A.inhab :=
begin
  apply classical.by_contradiction, intro hni, apply hA, rw eq_empty, intros z hz, apply hni, exact ⟨_, hz⟩,
end
theorem exists_unique_of_exists {p : Set → Prop} (h : ∃ x : Set, ∀ z, z ∈ x ↔ p z) : ∃! x : Set, ∀ z, z ∈ x ↔ p z :=
begin
  cases h with x h,
  refine ⟨x, h, (λ y H, _)⟩,
  refine ext (λ z, _),
  simp only [h z, H z],
end
theorem exists_unique_Inter {A : Set} (h : A.inhab) : ∃! B : Set, ∀ x, x ∈ B ↔ ∀ z ∈ A, x ∈ z :=
begin
  apply exists_unique_of_exists,
  cases h with c hin,
  refine ⟨{x ∈ c | ∀ z ∈ A, x ∈ z}, (λ z, _)⟩,
  simp only [mem_sep],
  split,
    rintro ⟨hz, ha⟩, exact ha,
  intro h,
  exact ⟨h c hin, h⟩,
end
theorem not_exists_Inter_empty : ¬ ∃ B : Set, ∀ x, x ∈ B ↔ ∀ z ∈ (∅ : Set), x ∈ z :=
begin
  rintro ⟨B, h⟩,
  apply univ_not_set,
  refine ⟨B, _⟩,
  intro x,
  specialize h x,
  rw h,
  intros a he,
  exfalso, exact mem_empty a he,
end
theorem no_abs_complement {A : Set} [decidable_pred (λ x, x ∈ A)] : ¬ ∃ B : Set, ∀ x, x ∈ B ↔ x ∉ A :=
begin
  rintro ⟨B, h⟩,
  apply univ_not_set,
  refine ⟨A ∪ B, _⟩,
  intro x,
  specialize h x,
  simp only [mem_union, h],
  exact decidable.em _,
end
theorem p10 {a B : Set} (h : a ∈ B) : a.powerset ∈ B.Union.powerset.powerset :=
begin
  rw mem_powerset,
  intros x h₂,
  rw mem_powerset at h₂,
  rw mem_powerset,
  intros z h₃,
  rw mem_Union,
  exact ⟨a, h, h₂ h₃⟩,
end

@[simp]
lemma mem_Inter {A x : Set} : x ∈ A.Inter ↔ A.inhab ∧ ∀ z ∈ A, x ∈ z :=
begin
  simp [Inter, mem_sep, inhab], intro ha, split,
  { rintro ⟨z, hz, hx⟩, exact ⟨_, hz⟩, },
  { rintro ⟨x, hx⟩, exact ⟨_, hx, ha _ hx⟩, },
end

lemma subset_self {A : Set} : A ⊆ A := (λ x hx, hx)

lemma eq_iff_subset_and_subset {A B : Set} : A = B ↔ A ⊆ B ∧ B ⊆ A :=
begin
  split, intro he, rw he, exact ⟨subset_self, subset_self⟩,
  rintro ⟨ha, hb⟩, apply ext, intro x, rw iff_iff_implies_and_implies, rw subset_def at *, exact ⟨@ha x, @hb x⟩,
end

lemma subset_trans {A B C : Set} (hA : A ⊆ B) (hB : B ⊆ C) : A ⊆ C := (λ x hx, hB (hA hx))

lemma subset_Union {X Y : Set} (h : X ∈ Y) : X ⊆ Y.Union :=
begin
  simp only [subset_def, mem_Union, exists_prop], exact (λ z hz, ⟨_, h, hz⟩),
end

lemma subset_Inter {X Y : Set} (h : X ∈ Y) : Y.Inter ⊆ X :=
begin
  simp only [subset_def, mem_Inter], exact (λ z ⟨hi, ha⟩, ha _ h),
end

lemma mem_powerset_self {X : Set} : X ∈ X.powerset :=
begin
  rw mem_powerset, exact subset_self,
end

@[simp]
lemma sep_subset {a : Set} {p : Set → Prop} : {x ∈ a | p x} ⊆ a := (λ x hx, (mem_sep.mp hx).left)

theorem p21 {A B : Set} : (A ∪ B).Union = A.Union ∪ B.Union :=
begin
  apply ext, simp only [exists_prop, mem_union, mem_Union], intro x, split,
  { rintro ⟨X, (hX|hX), hx⟩,
    { left, exact ⟨_, hX, hx⟩, },
    { right, exact ⟨_, hX, hx⟩, }, },
  { rintro (⟨X, hX, hx⟩|⟨X, hX, hx⟩),
    { exact ⟨_, or.inl hX, hx⟩, },
    { exact ⟨_, or.inr hX, hx⟩, }, },
end

lemma union_comm {x y : Set} : x ∪ y = y ∪ x :=
begin
  apply ext, simp only [mem_union, or_comm, forall_const, iff_self],
end

lemma union_empty {x : Set} : x ∪ ∅ = x :=
begin
  apply ext, simp only [mem_union, mem_empty, forall_const, iff_self, or_false],
end

lemma inter_comm {x y : Set} : x ∩ y = y ∩ x :=
begin
  apply ext, simp only [mem_inter, and_comm, iff_self, implies_true_iff],
end

lemma inter_union {A B C : Set} : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C :=
begin
  apply ext, simp only [and_or_distrib_left, forall_const, mem_inter, iff_self, mem_union],
end

lemma union_inter {A B C : Set} : (A ∪ B) ∩ C = A ∩ C ∪ B ∩ C :=
begin
  apply ext, simp only [mem_inter, mem_union, or_and_distrib_right, forall_const, iff_self],
end

lemma union_assoc {A B C : Set} : A ∪ (B ∪ C) = (A ∪ B) ∪ C :=
begin
  apply ext, simp only [mem_union, or_assoc, forall_const, iff_self],
end

lemma inter_empty {A : Set} : A ∩ ∅ = ∅ :=
begin
  simp only [eq_empty, mem_inter, mem_empty, forall_const, not_false_iff, and_false],
end

lemma subset_union_left {A B : Set} : A ⊆ A ∪ B := subset_union_of_subset subset_self

lemma subset_union_right {A B : Set} : B ⊆ A ∪ B := begin rw union_comm, exact subset_union_left, end

lemma union_subset_of_subset_of_subset {A B C : Set} (hA : A ⊆ C) (hB : B ⊆ C) : (A ∪ B) ⊆ C :=
begin
  intro x, rw mem_union, rintro (hx|hx),
  { exact hA hx, },
  { exact hB hx, },
end

lemma union_eq_union_diff {A B : Set} : A ∪ B = A ∪ (B \ A) :=
begin
  apply ext, simp only [mem_union, mem_diff, or_and_distrib_left, classical.em, forall_const, and_true, iff_self],
end

lemma subset_diff {A B : Set} : A \ B ⊆ A :=
begin
  intros x hx, rw mem_diff at hx, exact hx.left,
end

lemma self_inter_diff_empty {A B : Set} : A ∩ (B \ A) = ∅ :=
begin
  simp [eq_empty, mem_inter, mem_diff], intros x hA hB, exact hA,
end

lemma subset_Union_of_mem {X K : Set} (hXK : X ∈ K) : X ⊆ K.Union :=
begin
  intros z hz, rw mem_Union, exact ⟨_, hXK, hz⟩,
end

lemma Union_powerset_subset_self {X : Set} : X.powerset.Union ⊆ X :=
begin
  intros z hz, simp only [mem_Union, exists_prop, mem_powerset] at hz, rcases hz with ⟨Y, hYX, hzy⟩,
  exact hYX hzy,
end

lemma Union_subset_of_subset_powerset {X Y : Set} (h : X ⊆ Y.powerset) : X.Union ⊆ Y :=
begin
  intros x hx, rw mem_Union at hx, rcases hx with ⟨Z, hZX, hxZ⟩, specialize h hZX, rw mem_powerset at h,
  exact h hxZ,
end

end Set