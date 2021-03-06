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

lemma vacuous {p : Set → Prop} : ∀ x : Set, x ∈ (∅ : Set) → p x :=
begin
  intros x hx, exfalso, exact mem_empty _ hx,
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

lemma diff_ne_empty_of_ne {B A : Set} (hBA : B ⊆ A) (hne : B ≠ A) : (A \ B) ≠ ∅ :=
begin
  intro he, apply hne, rw eq_iff_subset_and_subset, refine ⟨hBA, _⟩,
  intros x hx, apply classical.by_contradiction, intro hxB,
  apply mem_empty x, rw ←he, rw mem_diff, exact ⟨hx, hxB⟩,
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

lemma subset_union_of_subset_left {A B C : Set} (hAB : A ⊆ B) : A ⊆ B ∪ C :=
begin intros x hx, rw mem_union, exact or.inl (hAB hx), end

lemma subset_union_of_subset_right {A B C : Set} (hAB : A ⊆ C) : A ⊆ B ∪ C :=
begin intros x hx, rw mem_union, exact or.inr (hAB hx), end

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

lemma union_eq_left_of_subset {A B : Set} (hBA : B ⊆ A) : A ∪ B = A :=
begin
  rw eq_iff_subset_and_subset,
  exact ⟨union_subset_of_subset_of_subset subset_self hBA, subset_union_left⟩,
end

lemma union_diff_eq_self_of_subset {A B : Set} (hAB : A ⊆ B) : A ∪ (B \ A) = B :=
begin
  rw [←union_eq_union_diff, eq_iff_subset_and_subset],
  exact ⟨union_subset_of_subset_of_subset hAB subset_self, subset_union_right⟩,
end

lemma diff_singleton_union_eq {A x : Set} (xA : x ∈ A) : (A \ {x}) ∪ {x} = A :=
begin
  rw union_comm, apply union_diff_eq_self_of_subset,
  intros z zx, rw mem_singleton at zx, subst zx, exact xA,
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

lemma diff_diff_eq_self_of_subset {A B : Set} (hBA : B ⊆ A) : A \ (A \ B) = B :=
begin
  apply ext, intro x, simp only [mem_diff], split,
    rintro ⟨hA, h⟩, apply classical.by_contradiction, intro hB, exact h ⟨hA, hB⟩,
  intro hB, refine ⟨hBA hB, _⟩, rintro ⟨hA, hB'⟩, exact hB' hB,
end

lemma empty_subset {A : Set} : ∅ ⊆ A :=
λ x : Set, assume hx : x ∈ ∅, show x ∈ A, from false.elim (mem_empty x hx)

lemma prod_subset_of_subset_of_subset {A B : Set} (hAB : A ⊆ B) {C D : Set} (hCD : C ⊆ D) : A.prod C ⊆ B.prod D :=
begin
  intros z hz, simp only [mem_prod, exists_prop] at *,
  rcases hz with ⟨a, ha, c, hc, he⟩,
  exact ⟨_, hAB ha, _, hCD hc, he⟩,
end

lemma inter_eq_of_subset {A B : Set} (hAB : A ⊆ B) : B ∩ A = A :=
begin
  apply ext, intro x, rw mem_inter, split,
    rintro ⟨hB, hA⟩, exact hA,
  intro hA, exact ⟨hAB hA, hA⟩,
end

lemma inter_subset_right {A B : Set} : A ∩ B ⊆ B :=
begin
  intros x xAB, rw mem_inter at xAB, exact xAB.right,
end

lemma inter_subset_left {A B : Set} : A ∩ B ⊆ A :=
begin
  intros x xAB, rw mem_inter at xAB, exact xAB.left,
end

lemma diff_sub_diff_of_sub {A B : Set} (AB : A ⊆ B) {C : Set} : C \ B ⊆ C \ A :=
begin
  intros x xCB, rw mem_diff at *, exact ⟨xCB.left, assume xA, xCB.right (AB xA)⟩,
end

lemma mem_sep' {X : Set} {p : Set → Prop} {x : Set} (xX : x ∈ X) : x ∈ {x ∈ X | p x} ↔ p x :=
by simp only [mem_sep, xX, true_and]

lemma inter_eq_of_sub {A B : Set} (AB : A ⊆ B) : A ∩ B = A :=
begin
  apply ext, intro x, rw mem_inter, split,
    rintro ⟨xA, -⟩, exact xA,
  intro xA, exact ⟨xA, AB xA⟩,
end

lemma singleton_ne_empty {x : Set} : ({x} : Set) ≠ ∅ :=
begin
  apply ne_empty_of_inhabited, use x, rw mem_singleton,
end

lemma sub_inter_of_sub {x a b : Set} (xa : x ⊆ a) (xb : x ⊆ b) : x ⊆ a ∩ b :=
begin
  intros z zx, rw mem_inter, exact ⟨xa zx, xb zx⟩,
end

lemma Union_sub_of_sub {A B : Set} (AB : A ⊆ B) : A.Union ⊆ B.Union :=
begin
  simp only [subset_def, mem_Union, exists_prop],
  rintros x ⟨y, yA, xy⟩, exact ⟨_, AB yA, xy⟩,
end

lemma Union_sub {A X : Set} (h : ∀ {x : Set}, x ∈ X → x ⊆ A) : X.Union ⊆ A :=
begin
  intro z, rw mem_Union, rintro ⟨x, xX, zx⟩, exact h xX zx,
end

lemma Union_diff_empty_eq {A : Set} : A.Union = (A \ {∅}).Union :=
begin
  apply ext, simp only [mem_Union, exists_prop, mem_diff, mem_singleton], intro x, split,
    rintro ⟨y, yA, xy⟩, refine ⟨_, ⟨yA, _⟩, xy⟩, apply ne_empty_of_inhabited, rw inhab, exact ⟨_, xy⟩,
  rintro ⟨y, ⟨yA, -⟩, xy⟩, finish,
end

lemma union_eq_Union {A B : Set} : A ∪ B = Union {A, B} :=
begin
  apply ext, simp only [mem_union, mem_Union, exists_prop, mem_insert, mem_singleton], intro x, split,
    finish,
  rintro ⟨z, (hz|hz), xz⟩; finish,
end

lemma Union_empty : Union ∅ = ∅ :=
begin
  rw eq_empty, intros z h, rw mem_Union at h, rcases h with ⟨x, h, -⟩, exact mem_empty _ h,
end

lemma inhab_of_Union_inhab {S : Set} (inh : S.Union.inhab) : S.inhab :=
begin
  obtain ⟨x, hx⟩ := inh, rw mem_Union at hx, rcases hx with ⟨y, yS, xy⟩,
  exact ⟨_, yS⟩,
end

end Set