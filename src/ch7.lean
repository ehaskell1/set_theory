import ch6
universe u
namespace Set

local attribute [irreducible] mem

structure part_order (R : Set) : Prop :=
(rel : R.is_rel)
(trans : R.transitive)
(irrefl : ∀ ⦃x : Set⦄, x.pair x ∉ R)

def part_le (R x y : Set) : Prop := x.pair y ∈ R ∨ x = y

-- Theorem 7A part a
theorem not_lt_and_gt_part {R : Set} (hR : R.part_order) {x y : Set} : ¬ (x.pair y ∈ R ∧ y.pair x ∈ R) :=
(assume h, hR.irrefl (hR.trans h.left h.right))

-- Theorem 7A part b
theorem eq_of_le_of_ge {R : Set} (hR : R.part_order) {x y : Set} (hxy : R.part_le x y) (hyx : R.part_le y x) : x = y :=
begin
  cases hxy,
    cases hyx,
      exfalso, exact not_lt_and_gt_part hR ⟨hxy, hyx⟩,
    exact hyx.symm,
  exact hxy,
end

lemma part_order_of_lin_order {A R : Set} (hR : A.lin_order R) : R.part_order :=
⟨λ z, assume hz, is_pair_of_mem_prod (hR.rel hz), hR.trans, hR.irrefl⟩

structure rel_struct :=
(fld rel : Set)
(is_rel : rel ⊆ fld.prod fld)

def is_least (D R m : Set) : Prop := ¬ ∃ x : Set, x ∈ D ∧ x.pair m ∈ R

theorem least_unique {A R : Set} (lin : A.lin_order R) {D : Set} (DA : D ⊆ A) {m n : Set} (mD : m ∈ D) (nD : n ∈ D)
  (ml : D.is_least R m) (nl : D.is_least R n) : m = n :=
begin
  apply classical.by_contradiction, intro mn,
  cases lin.conn (DA mD) (DA nD) mn with mln nlm,
    exact nl ⟨_, mD, mln⟩,
  exact ml ⟨_, nD, nlm⟩,
end

structure well_order (A R : Set) : Prop :=
(lin : A.lin_order R)
(well : ∀ ⦃X : Set⦄, X ≠ ∅ → X ⊆ A → ∃ m : Set, m ∈ X ∧ X.is_least R m)

-- Theorem 7B
theorem well_order_iff_not_exists_desc_chain {A R : Set} (hlin : A.lin_order R) :
A.well_order R ↔ ¬ ∃ f : Set, f.into_fun ω A ∧ ∀ ⦃n : Set⦄, n ∈ ω → (f.fun_value n.succ).pair (f.fun_value n) ∈ R :=
begin
  split,
    rintros hwell ⟨f, finto, hf⟩,
    have hran : f.ran ≠ ∅, apply ne_empty_of_inhabited, use f.fun_value ∅,
      apply fun_value_def'' finto.left, rw finto.right.left, exact zero_nat,
    obtain ⟨m, hm, hl⟩ := hwell.well hran finto.right.right,
    obtain ⟨x, hx, he⟩ := eq_fun_value_of_mem_ran finto.left hm, subst he,
    apply hl, use f.fun_value x.succ, split,
      apply fun_value_def'' finto.left, rw finto.right.left at *, exact nat_induct.succ_closed hx,
    rw finto.right.left at hx, exact hf hx,
  intro ne, apply classical.by_contradiction, intro nw, apply ne,
  have h : ¬ ∀ ⦃X : Set⦄, X ≠ ∅ → X ⊆ A → ∃ m : Set, m ∈ X ∧ X.is_least R m,
    intro h, apply nw, exact ⟨hlin, h⟩,
  dsimp [is_least] at h, push_neg at h, rcases h with ⟨X, ne, hX, h⟩,
  have Rrel : R.is_rel := λ z hz, is_pair_of_mem_prod (hlin.rel hz),
  obtain ⟨f, finto, hf⟩ := exists_desc_chain_of_no_least ne Rrel h,
  exact ⟨f, into_of_into_ran_sub hX finto, hf⟩,
end

def seg (R t : Set) : Set := {x ∈ R.dom | x.pair t ∈ R}

@[simp]
lemma mem_seg {R t x : Set} : x ∈ R.seg t ↔ x.pair t ∈ R :=
begin
  simp only [seg, mem_sep, mem_dom, and_iff_right_iff_imp], intro hxt, exact ⟨_, hxt⟩,
end

-- example
lemma seg_nat {n : Set} (hn : n ∈ ω) : (pair_sep (λ m n, m ∈ n) ω ω).seg n = n :=
begin
  apply ext, intro m, simp only [mem_seg, pair_mem_pair_sep], split,
    rintro ⟨-, -, hmn⟩, exact hmn,
  intro hmn, exact ⟨mem_nat_of_mem_nat_of_mem hn hmn, hn, hmn⟩,
end

def ind (A R B : Set) : Prop := ∀ ⦃t : Set⦄, t ∈ A → R.seg t ⊆ B → t ∈ B

theorem transfinite_ind {A R : Set} (hwell : A.well_order R) {B : Set} (hBA : B ⊆ A) (h : A.ind R B) : B = A :=
begin
  apply classical.by_contradiction, intro hne,
  have dne := diff_ne_empty_of_ne hBA hne,
  obtain ⟨m, hmB, hl⟩ := hwell.well dne subset_diff,
  rw mem_diff at hmB, apply hmB.right, apply h hmB.left,
  intros y hy, rw mem_seg at hy, apply classical.by_contradiction, intro hyB,
  apply hl, refine ⟨_, _, hy⟩, rw mem_diff, refine ⟨_, hyB⟩,
  have hz : y.pair m ∈ A.prod A := hwell.lin.rel hy,
  rw pair_mem_prod at hz, exact hz.left,
end

-- Theorem 7C
theorem transfinite_ind_conv {A R : Set} (hlin : A.lin_order R) (h : ∀ ⦃B : Set⦄, B ⊆ A → A.ind R B → B = A) : A.well_order R :=
begin
  refine ⟨hlin, _⟩, intros C hC hCA,
  let B : Set := {t ∈ A | ∀ {x}, x ∈ C → t.pair x ∈ R},
  have hBC : B ∩ C = ∅, rw eq_empty, intros t ht, rw [mem_inter, mem_sep] at ht,
    exact hlin.irrefl (ht.left.right ht.right),
  have hBA : B ⊆ A := sep_subset,
  by_cases hcase : A.ind R B,
    rw h hBA hcase at hBC, exfalso, apply hC, rw eq_empty, intros x hx, apply mem_empty x, rw [←hBC, mem_inter],
    exact ⟨hCA hx, hx⟩,
  dsimp [ind] at hcase, push_neg at hcase, rcases hcase with ⟨t, htA, hseg, htB⟩, use t, split,
    rw [mem_sep] at htB, push_neg at htB,
    obtain ⟨x, hxC, htx⟩ := htB htA,
    have hxt : x = t, apply classical.by_contradiction, intro hxt,
      cases hlin.conn (hCA hxC) htA hxt with hxt' hxt',
        apply mem_empty x, rw [←hBC, mem_inter], split,
          apply hseg, rw mem_seg, exact hxt',
        exact hxC,
      exact htx hxt',
    subst hxt, exact hxC,
  rintro ⟨x, hxC, hxt⟩, apply mem_empty x, rw [←hBC, mem_inter], split,
    apply hseg, rw mem_seg, exact hxt,
  exact hxC,
end

def lin_le (R x y : Set) : Prop := x.pair y ∈ R ∨ x = y

lemma le_iff_not_lt {A R : Set} (hlin : A.lin_order R) {x : Set} (hx : x ∈ A) {y : Set} (hy : y ∈ A) :
R.lin_le x y ↔ ¬ y.pair x ∈ R :=
begin
  split,
    rintro (hxy|hxy); intro hyx,
      exact hlin.irrefl (hlin.trans hxy hyx),
    subst hxy, exact hlin.irrefl hyx,
  intro hyx, by_cases hc : x = y,
    exact or.inr hc,
  cases hlin.conn hx hy hc,
    exact or.inl h,
  exfalso, exact hyx h,
end

lemma lt_iff_not_le {A R : Set} (hlin : A.lin_order R) {x : Set} (hx : x ∈ A) {y : Set} (hy : y ∈ A) :
x.pair y ∈ R ↔ ¬ R.lin_le y x :=
begin
  rw le_iff_not_lt hlin hy hx, simp only [not_not],
end

lemma mem_fld_of_lt {A R : Set} (hlin : A.lin_order R) {x y : Set} (hxy : x.pair y ∈ R) : x ∈ A :=
begin
  have hxy' : x.pair y ∈ A.prod A := hlin.rel hxy,
  rw pair_mem_prod at hxy', exact hxy'.left,
end

lemma mem_fld_of_le {A R : Set} (hlin : A.lin_order R) {y : Set} (hy : y ∈ A) {x : Set} (hxy : R.lin_le x y) : x ∈ A :=
begin
  cases hxy,
    exact mem_fld_of_lt hlin hxy,
  subst hxy, exact hy,
end

lemma lt_or_le {A R : Set} (hlin : A.lin_order R) {x : Set} (hx : x ∈ A) {y : Set} (hy : y ∈ A) :
  x.pair y ∈ R ∨ R.lin_le y x :=
begin
  by_cases hxy : x.pair y ∈ R,
    exact or.inl hxy,
  rw ←le_iff_not_lt hlin hy hx at hxy, exact or.inr hxy,
end

lemma le_or_le {A R : Set} (hlin : A.lin_order R) {x : Set} (hx : x ∈ A) {y : Set} (hy : y ∈ A) :
  R.lin_le x y ∨ R.lin_le y x :=
begin
  cases lt_or_le hlin hx hy,
    left, left, exact h,
  right, exact h,
end

lemma lt_of_le_of_lt {A R : Set} (hlin : A.lin_order R) {x y : Set} (hxy : R.lin_le x y) {z : Set} (hyz : y.pair z ∈ R) :
  x.pair z ∈ R :=
begin
  cases hxy,
    exact hlin.trans hxy hyz,
  subst hxy, exact hyz,
end

lemma lt_of_lt_of_le {A R : Set} (hlin : A.lin_order R) {x y : Set} (hxy : x.pair y ∈ R) {z : Set} (hyz : R.lin_le y z) :
  x.pair z ∈ R :=
begin
  cases hyz,
    exact hlin.trans hxy hyz,
  subst hyz, exact hxy,
end

lemma le_of_le_of_le {A R : Set} (hlin : A.lin_order R) {x y : Set} (hxy : R.lin_le x y) {z : Set} (hyz : R.lin_le y z) :
  R.lin_le x z :=
begin
  cases hxy,
    left, exact lt_of_lt_of_le hlin hxy hyz,
  subst hxy, exact hyz,
end

lemma seg_subset_seg {A R : Set} (hlin : A.lin_order R) {x t : Set} (hxt : x.pair t ∈ R) : R.seg x ⊆ R.seg t :=
begin
  intros z hz, rw mem_seg at *, exact hlin.trans hz hxt,
end

lemma seg_subset_seg_of_le {A R : Set} (hlin : A.lin_order R) {x y : Set} (hxy : R.lin_le x y)
  : R.seg x ⊆ R.seg y :=
begin
  cases hxy,
    exact seg_subset_seg hlin hxy,
  subst hxy, exact subset_self,
end

lemma seg_inter_of_lt {A R : Set} (hlin : A.lin_order R) {x t : Set} (hxt : x.pair t ∈ R) : {t} ∩ R.seg x = ∅ :=
begin
  rw eq_empty, intros z hz, rw [mem_inter, mem_seg, mem_singleton] at hz, rcases hz with ⟨he, hzx⟩, subst he,
  exact hlin.irrefl (hlin.trans hzx hxt),
end

lemma seg_inter {A R : Set} (hlin : A.lin_order R) {x : Set} : {x} ∩ R.seg x = ∅ :=
begin
  rw eq_empty, intros z hz, rw [mem_inter, mem_singleton, mem_seg] at hz, cases hz with he hzx,
  subst he, exact hlin.irrefl hzx,
end

lemma mem_fld_of_pair_mem_rel_struct {R : rel_struct} {x y : Set} (hxy : x.pair y ∈ R.rel) : x ∈ R.fld ∧ y ∈ R.fld :=
begin
  replace hxy := R.is_rel hxy, rw pair_mem_prod at hxy, exact hxy,
end

lemma seg_sub_fld {R : rel_struct} {t : Set} (tA : t ∈ R.fld) : R.rel.seg t ⊆ R.fld :=
begin
  intros x xt, rw mem_seg at xt, exact (mem_fld_of_pair_mem_rel_struct xt).left,
end

local attribute [instance] classical.prop_decidable
local attribute [instance] classical.all_definable

theorem replacement {p : Set.{u} → Set.{u} → Prop} {A : Set.{u}}
(h : ∀ ⦃x : Set⦄, x ∈ A → ∃! y : Set, p x y) :
∃ B : Set.{u}, ∀ {y : Set.{u}}, y ∈ B ↔ ∃ x : Set, x ∈ A ∧ p x y :=
begin
  have hch : ∀ x : {x : Set // x ∈ A}, ∃ y : Set, p x.val y := λ ⟨x, hx⟩, exists_of_exists_unique (h hx),
  obtain ⟨g, hg⟩ := classical.axiom_of_choice hch,
  use A.image (λ x, if hx : x ∈ A then g ⟨x, hx⟩ else ∅), intro y,
  simp only [mem_image, exists_prop], split,
    rintro ⟨x, hx, he⟩, simp only [hx, dif_pos] at he, rw ←he, exact ⟨x, hx, hg ⟨x, hx⟩⟩,
  rintro ⟨x, hx, pxy⟩, refine ⟨x, hx, _⟩, simp only [hx, dif_pos],
  exact unique_of_exists_unique (h hx) (hg ⟨x, hx⟩) pxy,
end

theorem replacement' {p : Set.{u} → Set.{u} → Prop} {A : Set.{u}}
(h : ∀ ⦃x : Set⦄, x ∈ A → ∀ {y₁ : Set}, p x y₁ → ∀ {y₂ : Set}, p x y₂ → y₁ = y₂) :
∃ B : Set.{u}, ∀ {y : Set.{u}}, y ∈ B ↔ ∃ x : Set, x ∈ A ∧ p x y :=
begin
  let q : Set → Set → Prop := λ x y, p x y ∨ (¬ ∃ y, p x y) ∧ y = ∅,
  have h : ∀ x : Set, x ∈ A → ∃! y : Set, q x y, intros x hx, by_cases hc : ∃ y, p x y,
      rcases hc with ⟨y, pxy⟩, refine ⟨_, or.inl pxy, _⟩, rintros y' (pxy'|hc),
        exact h hx pxy' pxy,
      exfalso, exact hc.left ⟨_, pxy⟩,
    refine ⟨_, or.inr ⟨hc, rfl⟩, _⟩, rintros y' (pxy'|hc),
      exfalso, exact hc ⟨_, pxy'⟩,
    exact hc.right,
  obtain ⟨B, hB⟩ := replacement h,
  use {y ∈ B | ∃ x, x ∈ A ∧ p x y}, intro y, rw [mem_sep, hB],
  simp only [and_imp, and_iff_right_iff_imp, exists_imp_distrib],
  intros x hx pxy, exact ⟨_, hx, or.inl pxy⟩,
end

theorem replacement'' (f : Set.{u} → Set.{u}) {A : Set.{u}} :
∃ B : Set.{u}, ∀ {y : Set.{u}}, y ∈ B ↔ ∃ x : Set, x ∈ A ∧ y = f x :=
begin
  apply replacement, intros x xA, exact exists_unique_eq f _,
end

theorem transfinite_rec {p : Set.{u} → Set.{u} → Prop} {A R : Set.{u}} (hwell : A.well_order R)
(h : ∀ f : Set, ∃! y, p f y)
: ∃! F : Set, F.is_function ∧ F.dom = A ∧ ∀ ⦃t : Set⦄, t ∈ A → p (F.restrict (R.seg t)) (F.fun_value t) :=
begin
  let pcon : Set.{u} → Set.{u} → Prop := (λ t v, (∀ ⦃x : Set.{u}⦄, x ∈ v.dom ↔ R.lin_le x t)
    ∧ ∀ ⦃x : Set⦄, x ∈ v.dom → p (v.restrict (R.seg x)) (v.fun_value x)),
  let φ := (λ t v : Set.{u}, v.is_function ∧ pcon t v),
  have prerepl : ∀ {t₁ t₂ : Set}, R.lin_le t₁ t₂ → ∀ {v₁ : Set}, φ t₁ v₁ → ∀ {v₂ : Set}, φ t₂ v₂
    → ∀ {x : Set}, x ∈ A → R.lin_le x t₁ → v₁.fun_value x = v₂.fun_value x,
    intros t₁ t₂ htt v₁ φ₁ v₂ φ₂, refine classical.by_contradiction _, intros hex,
    push_neg at hex,
    let X := {x ∈ A | R.lin_le x t₁ ∧ v₁.fun_value x ≠ v₂.fun_value x},
    replace hex : ∃ x : Set, x ∈ X,
      rcases hex with ⟨x, hx, hne⟩, use x, rw mem_sep, exact ⟨hx, hne⟩,
    obtain ⟨x, hx, hle⟩ := hwell.well (ne_empty_of_inhabited X hex) (sep_subset),
    have he : v₁.restrict (R.seg x) = v₂.restrict (R.seg x),
      have hsub₁ : R.seg x ⊆ v₁.dom, intros z hz, rw φ₁.right.left, rw mem_seg at hz, left,
        rw mem_sep at hx, exact lt_of_lt_of_le hwell.lin hz hx.right.left,
      have hsub₂ : R.seg x ⊆ v₂.dom, intros z hz, rw φ₂.right.left, rw mem_seg at hz, left,
        rw mem_sep at hx, exact lt_of_lt_of_le hwell.lin (lt_of_lt_of_le hwell.lin hz hx.right.left) htt,
      apply fun_ext (restrict_is_function φ₁.left) (restrict_is_function φ₂.left),
        rw [restrict_dom hsub₁, restrict_dom hsub₂],
      intros z hz, rw restrict_dom hsub₁ at hz,
      rw [restrict_fun_value φ₁.left hsub₁ hz, restrict_fun_value φ₂.left hsub₂ hz],
      apply classical.by_contradiction, intro hne, apply hle, rw mem_seg at hz,
      have hzX : z ∈ X, rw mem_sep, rw mem_sep at hx,
        exact ⟨mem_fld_of_lt hwell.lin hz, or.inl (lt_of_lt_of_le hwell.lin hz hx.right.left), hne⟩,
      exact ⟨_, hzX, hz⟩,
    rw mem_sep at hx, apply hx.right.right,
    have hx₁ : x ∈ v₁.dom, rw φ₁.right.left, exact hx.right.left,
    have hx₂ : x ∈ v₂.dom, rw φ₂.right.left, exact le_of_le_of_le hwell.lin hx.right.left htt,
    apply unique_of_exists_unique (h (v₁.restrict (R.seg x))) (φ₁.right.right hx₁),
    rw he, exact φ₂.right.right hx₂,
  have hrepl : ∀ ⦃t : Set⦄, t ∈ A → ∀ {v₁ : Set}, φ t v₁ → ∀ {v₂ : Set}, φ t v₂ → v₁ = v₂,
    intros t ht v₁ hv₁ v₂ hv₂, apply fun_ext hv₁.left hv₂.left,
      apply ext, simp only [hv₁.right.left, hv₂.right.left, forall_const, iff_self],
    intros x hx, rw hv₁.right.left at hx,
    have hxA : x ∈ A := mem_fld_of_le hwell.lin ht hx,
    exact prerepl (or.inr rfl) hv₁ hv₂ hxA hx,
  obtain ⟨H, hH⟩ := replacement' hrepl,
  let F := H.Union,
  have hstar : ∀ {x y : Set}, x.pair y ∈ F ↔ ∃ v : Set, v ∈ H ∧ x.pair y ∈ v,
    simp only [mem_Union, exists_prop, forall_const, iff_self],
  have hfun : F.is_function, rw is_function_iff, split,
      apply Union_is_rel, intros v vH, simp only [hH, φ] at vH,
      rcases vH with ⟨-, -, vfun, -⟩, exact vfun.left,
    simp only [hstar, hH, φ], rintros x y₁ y₂ ⟨v₁, ⟨t₁, ht₁, vfun₁, pcon₁⟩, hxy₁⟩ ⟨v₂, ⟨t₂, ht₂, vfun₂, pcon₂⟩, hxy₂⟩,
    rw [fun_value_def vfun₁ hxy₁, fun_value_def vfun₂ hxy₂],
    have hx₁ : R.lin_le x t₁, rw [←pcon₁.left, mem_dom], exact ⟨_, hxy₁⟩,
    have hx₂ : R.lin_le x t₂, rw [←pcon₂.left, mem_dom], exact ⟨_, hxy₂⟩,
    have hx : x ∈ A := mem_fld_of_le hwell.lin ht₁ hx₁,
    cases le_or_le hwell.lin ht₁ ht₂ with htt htt,
      exact prerepl htt ⟨vfun₁, pcon₁⟩ ⟨vfun₂, pcon₂⟩ hx hx₁,
    symmetry, exact prerepl htt ⟨vfun₂, pcon₂⟩ ⟨vfun₁, pcon₁⟩ hx hx₂,
  have hpcon : ∀ ⦃x : Set⦄, x ∈ F.dom → p (F.restrict (R.seg x)) (F.fun_value x), intros x hx,
    simp only [mem_dom, hstar] at hx, rcases hx with ⟨y, v, vH, hxy⟩,
    have vH' := vH, simp only [hH, φ, pcon, mem_dom] at vH',
    rcases vH' with ⟨t, ht, vfun, vdom, hp⟩, specialize hp ⟨_, hxy⟩,
    have he : v.restrict (R.seg x) = F.restrict (R.seg x),
      have hsub : R.seg x ⊆ v.dom, intros z hz, rw [mem_dom, vdom], left, rw mem_seg at hz,
        have hxt := (@vdom _).mp ⟨_, hxy⟩,
        exact lt_of_lt_of_le hwell.lin hz hxt,
      have hsub' : R.seg x ⊆ F.dom, intros z hz, simp only [mem_dom, hstar],
        have hz' : z ∈ v.dom, rw [mem_dom, vdom], left, rw mem_seg at hz,
          have hxt := (@vdom _).mp ⟨_, hxy⟩,
          exact lt_of_lt_of_le hwell.lin hz hxt,
        rw mem_dom at hz', rcases hz' with ⟨y', hzy⟩, exact ⟨_, _, vH, hzy⟩,
      apply fun_ext (restrict_is_function vfun) (restrict_is_function hfun),
        rw [restrict_dom hsub, restrict_dom hsub'],
      intros z hz, rw restrict_dom hsub at hz,
      rw [restrict_fun_value vfun hsub hz, restrict_fun_value hfun hsub' hz],
      apply fun_value_def hfun, rw hstar, refine ⟨_, vH, _⟩, apply fun_value_def' vfun,
      rw [mem_dom, vdom], left, rw mem_seg at hz,
      have hxt := (@vdom _).mp ⟨_, hxy⟩,
      exact lt_of_lt_of_le hwell.lin hz hxt,
    have he' : v.fun_value x = F.fun_value x,
      apply fun_value_def hfun, rw hstar, refine ⟨_, vH, _⟩, apply fun_value_def' vfun,
      rw mem_dom, exact ⟨_, hxy⟩,
    rw [he, he'] at hp, exact hp,
  have hdom : F.dom = A, rw eq_iff_subset_and_subset, split,
      intros x hx, rw [mem_dom] at hx, simp only [hstar, hH, φ, pcon] at hx,
      rcases hx with ⟨y, v, ⟨t, ht, vfun, hv, hv'⟩, hxy⟩,
      have hx' : x ∈ v.dom, rw mem_dom, exact ⟨_, hxy⟩,
      rw hv at hx', exact mem_fld_of_le hwell.lin ht hx',
    apply @classical.by_contradiction (A ⊆ F.dom), intros hin, rw subset_def at hin, push_neg at hin,
    replace hin : (A \ F.dom) ≠ ∅, apply ne_empty_of_inhabited, simp only [inhab, mem_diff], exact hin,
    obtain ⟨t, ht, hle⟩ := hwell.well hin subset_diff,
    rw mem_diff at ht,
    have hdom : R.seg t = F.dom, rw eq_iff_subset_and_subset, split,
        intros x hx, rw mem_seg at hx, apply classical.by_contradiction, intro hxF, apply hle,
        use x, rw mem_diff, exact ⟨⟨mem_fld_of_lt hwell.lin hx, hxF⟩, hx⟩,
      intros x hx, simp only [mem_dom, hstar] at hx, rcases hx with ⟨y, v, vH, hxy⟩,
      have vH' := vH, simp only [hH, φ, pcon, mem_dom] at vH',
      rcases vH' with ⟨t', ht', -, hv, -⟩,
      cases lt_or_le hwell.lin ht' ht.left with htt htt,
        rw mem_seg, replace hxy := (@hv _).mp ⟨_, hxy⟩, exact lt_of_le_of_lt hwell.lin hxy htt,
      rw ←hv at htt, cases htt with y' hty, exfalso, apply ht.right,
      simp only [mem_dom, hstar], exact ⟨_, _, vH, hty⟩,
    rcases exists_of_exists_unique (h F) with ⟨y, hy⟩, apply ht.right,
    simp only [mem_dom, hstar, hH, φ, pcon], use y, use F ∪ {t.pair y}, rw and_comm, split,
      rw [mem_union, mem_singleton], right, refl,
    use t, split,
      exact ht.left,
    split, exact union_singleton_is_fun hfun ht.right, split, simp only [←mem_dom],
      simp only [union_dom, mem_union, mem_singleton, ←hdom, dom_singleton, lin_le, mem_seg, forall_const, iff_self],
    simp only [←mem_dom], simp only [union_dom, ←hdom, dom_singleton, mem_union, mem_singleton, mem_seg],
    rintros x (hxt|hxt),
      have hsub : R.seg x ⊆ F.dom, rw ←hdom, exact seg_subset_seg hwell.lin hxt,
      have hsub' : R.seg x ⊆ (F ∪ {t.pair y}).dom, rw [union_dom, dom_singleton], exact subset_union_of_subset_left hsub,
      have he : (F ∪ {t.pair y}).restrict (R.seg x) = F.restrict (R.seg x),
        apply fun_ext (restrict_is_function (union_singleton_is_fun hfun ht.right)) (restrict_is_function hfun),
          simp only [restrict_dom_inter, union_dom, dom_singleton, ←hdom, union_inter, seg_inter_of_lt hwell.lin hxt, union_empty],
        simp only [restrict_dom_inter, union_dom, dom_singleton, ←hdom, union_inter],
        simp only [seg_inter_of_lt hwell.lin hxt, union_empty, inter_eq_of_subset (seg_subset_seg hwell.lin hxt)],
        intros z hz,
        rw restrict_fun_value (union_singleton_is_fun hfun ht.right) hsub' hz,
        rw restrict_fun_value hfun hsub hz, symmetry, apply fun_value_def (union_singleton_is_fun hfun ht.right),
        rw mem_union, left, apply fun_value_def' hfun, rw ←hdom, exact (seg_subset_seg hwell.lin hxt) hz,
      have he' : (F ∪ {t.pair y}).fun_value x = F.fun_value x, symmetry,
        apply fun_value_def (union_singleton_is_fun hfun ht.right), rw mem_union, left,
        apply fun_value_def' hfun, rw [←hdom, mem_seg], exact hxt,
      rw [he, he'],
      have hx : x ∈ F.dom, rw [←hdom, mem_seg], exact hxt,
      exact hpcon hx,
    subst hxt,
    have he : (F ∪ {x.pair y}).restrict (R.seg x) = F,
      apply fun_ext (restrict_is_function (union_singleton_is_fun hfun ht.right)) hfun,
        rw [restrict_dom_inter, union_dom, dom_singleton, union_inter, seg_inter hwell.lin, union_empty, hdom],
        rw inter_eq_of_subset subset_self,
      intros z hz,
        rw [restrict_dom_inter, union_dom, dom_singleton, union_inter, seg_inter hwell.lin, union_empty, hdom, inter_eq_of_subset subset_self] at hz,
        have hsub : R.seg x ⊆ (F ∪ {x.pair y}).dom, rw [union_dom, dom_singleton, hdom], exact subset_union_left,
        rw ←hdom at hz, rw restrict_fun_value (union_singleton_is_fun hfun ht.right) hsub hz, symmetry,
        apply fun_value_def (union_singleton_is_fun hfun ht.right), rw mem_union, left,
        apply fun_value_def' hfun, rw ←hdom, exact hz,
    have he' : (F ∪ {x.pair y}).fun_value x = y, symmetry,
      apply fun_value_def (union_singleton_is_fun hfun ht.right), rw [mem_union, mem_singleton], right, refl,
    rw [he, he'], exact hy,
  rw hdom at hpcon,
  refine exists_unique_of_exists_of_unique ⟨_, hfun, hdom, hpcon⟩ _,
  rintros F F' ⟨Ffun, Fdom, hF⟩ ⟨Ffun', Fdom', hF'⟩,
  let B : Set := {t ∈ A | F.fun_value t = F'.fun_value t},
  suffices hBA : B = A, apply fun_ext Ffun Ffun',
      rw [Fdom, Fdom'],
    intros x hx, rw [Fdom, ←hBA, mem_sep] at hx, exact hx.right,
  apply transfinite_ind hwell sep_subset, intros t htA ht, rw mem_sep, refine ⟨htA, _⟩,
  have he : F.restrict (R.seg t) = F'.restrict (R.seg t),
    apply fun_ext (restrict_is_function Ffun) (restrict_is_function Ffun'),
      simp only [restrict_dom_inter, Fdom, Fdom'],
    intros x hx, rw [restrict_dom_inter, mem_inter] at hx,
    rw restrict_fun_value' Ffun hx.left hx.right,
    rw [Fdom, ←Fdom'] at hx,
    rw restrict_fun_value' Ffun' hx.left hx.right,
    specialize ht hx.right, rw mem_sep at ht, exact ht.right,
  specialize hF htA, specialize hF' htA, rw he at hF,
  exact unique_of_exists_unique (h _) hF hF',
end
-- I think that was the longest proof yet...

theorem transfinite_rec' {A R : Set.{u}} (hwell : A.well_order R) (f : Set.{u} → Set.{u})
: ∃! F : Set, F.is_function ∧ F.dom = A ∧ ∀ ⦃t : Set⦄, t ∈ A → (F.fun_value t) = f (F.restrict (R.seg t)) :=
transfinite_rec hwell (exists_unique_eq f)

noncomputable def eps_img_fun (R : rel_struct) : Set :=
if case : R.fld.well_order R.rel then
  classical.some (exists_of_exists_unique (@transfinite_rec (λ f y, y = f.ran) _ _ case (exists_unique_eq ran)))
else
  ∅

lemma eps_img_fun_spec {R : rel_struct} (well : R.fld.well_order R.rel) :
  (eps_img_fun R).is_function ∧ (eps_img_fun R).dom = R.fld
  ∧ ∀ ⦃t : Set⦄, t ∈ R.fld → (eps_img_fun R).fun_value t = ((eps_img_fun R).restrict (R.rel.seg t)).ran :=
begin
  simp only [eps_img_fun, well, dif_pos],
  exact classical.some_spec (exists_of_exists_unique (@transfinite_rec (λ f y, y = f.ran) _ _ well (exists_unique_eq ran))),
end

lemma eps_img_fun_value_img {R : rel_struct} (well : R.fld.well_order R.rel) {t : Set} (ht : t ∈ R.fld) :
  (eps_img_fun R).fun_value t = (eps_img_fun R).img (R.rel.seg t) :=
begin
  obtain ⟨-, -, h⟩ := eps_img_fun_spec well,
  rw [img, h ht],
end

lemma mem_eps_img_fun {R : rel_struct} (well : R.fld.well_order R.rel) {t : Set} (ht : t ∈ R.fld) {y : Set} :
  y ∈ (eps_img_fun R).fun_value t ↔ ∃ x : Set, x.pair t ∈ R.rel ∧ y = (eps_img_fun R).fun_value x :=
begin
  obtain ⟨f, dom, -⟩ := eps_img_fun_spec well,
  have sub : R.rel.seg t ⊆ (eps_img_fun R).dom, intros x hx, rw mem_seg at hx,
    replace hx := (mem_fld_of_pair_mem_rel_struct hx).left, rw dom, exact hx,
  simp only [eps_img_fun_value_img well ht, mem_img' f sub, mem_seg],
end

lemma fun_value_mem_eps_img_fun {R : rel_struct} (well : R.fld.well_order R.rel) {t : Set} (ht : t ∈ R.fld) {x : Set} (hx : x.pair t ∈ R.rel) :
  (eps_img_fun R).fun_value x ∈ (eps_img_fun R).fun_value t :=
begin
  rw mem_eps_img_fun well ht, exact ⟨_, hx, rfl⟩,
end

noncomputable def eps_img (R : rel_struct) : Set := (eps_img_fun R).ran

@[simp]
lemma mem_eps_img {R : rel_struct} (well : R.fld.well_order R.rel) {y : Set} :
  y ∈ eps_img R ↔ ∃ x : Set, x ∈ R.fld ∧ y = (eps_img_fun R).fun_value x :=
begin
  obtain ⟨f, dom, -⟩ := eps_img_fun_spec well,
  rw [eps_img, mem_ran_iff f, dom],
end

lemma fun_value_mem_eps_img {R : rel_struct} (well : R.fld.well_order R.rel) {x : Set} (hx : x ∈ R.fld) :
  (eps_img_fun R).fun_value x ∈ eps_img R :=
begin
  rw mem_eps_img well, exact ⟨_, hx, rfl⟩,
end

-- Theorem 7D part a
theorem eps_img_fun_irrefl {R : rel_struct} (well : R.fld.well_order R.rel) {t : Set} (tA : t ∈ R.fld) :
  (eps_img_fun R).fun_value t ∉ (eps_img_fun R).fun_value t :=
begin
  let S := {x ∈ R.fld | (eps_img_fun R).fun_value x ∈ (eps_img_fun R).fun_value x},
  intro ftt,
  have SE : S ≠ ∅, apply ne_empty_of_inhabited, use t, rw mem_sep, exact ⟨tA, ftt⟩,
  obtain ⟨m, mS, le⟩ := well.well SE sep_subset,
  rw [mem_sep] at mS, obtain ⟨mA, fmm⟩ := mS,
  have fmm' := fmm, rw mem_eps_img_fun well mA at fmm', obtain ⟨x, xm, fmx⟩ := fmm',
  have xA := (mem_fld_of_pair_mem_rel_struct xm).left,
  apply le, use x, rw mem_sep, rw ←fmx, exact ⟨⟨xA, fmm⟩, xm⟩,
end

-- Theorem 7D part b part 1
theorem eps_img_fun_onto {R : rel_struct} (well : R.fld.well_order R.rel) : (eps_img_fun R).onto_fun R.fld (eps_img R) :=
begin
  obtain ⟨f, dom, -⟩ := eps_img_fun_spec well,
  rw [eps_img, ←dom], exact ⟨f, rfl, rfl⟩,
end

-- Theorem 7D part b part 2
theorem eps_img_fun_oto {R : rel_struct} (well : R.fld.well_order R.rel) : (eps_img_fun R).one_to_one :=
begin
  obtain ⟨f, dom, -⟩ := eps_img_fun_spec well,
  apply one_to_one_of f, rw dom, intros s sA t tA st fst,
  cases well.lin.conn sA tA st with slt tls,
    have fslt := fun_value_mem_eps_img_fun well tA slt,
    rw fst at fslt, exact eps_img_fun_irrefl well tA fslt,
  have ftls := fun_value_mem_eps_img_fun well sA tls,
  rw fst at ftls, exact eps_img_fun_irrefl well tA ftls,
end

-- Theorem 7D part c
theorem fun_value_mem_eps_img_fun_iff {R : rel_struct} (well : R.fld.well_order R.rel) {s : Set} (sA : s ∈ R.fld) {t : Set} (tA : t ∈ R.fld) :
  (eps_img_fun R).fun_value s ∈ (eps_img_fun R).fun_value t ↔ s.pair t ∈ R.rel :=
begin
  obtain ⟨f, dom, _⟩ := eps_img_fun_spec well,
  split,
    intro fst, rw mem_eps_img_fun well tA at fst,
    obtain ⟨x, xt, fsx⟩ := fst,
    have xA := (mem_fld_of_pair_mem_rel_struct xt).left,
    rw ←dom at sA xA,
    rw from_one_to_one f (eps_img_fun_oto well) xA sA fsx.symm at xt,
    exact xt,
  intro st, exact fun_value_mem_eps_img_fun well tA st,
end

-- Theorem 7D part d
theorem eps_img_transitive {R : rel_struct} (well : R.fld.well_order R.rel) :
  (eps_img R).transitive_set :=
begin
  intros y yf, rw mem_Union at yf, obtain ⟨Y, Yf, yY⟩ := yf,
  rw mem_eps_img well at Yf, obtain ⟨t, tf, Yt⟩ := Yf, subst Yt,
  obtain ⟨f, dom, spec⟩ := eps_img_fun_spec well, rw [spec tf, mem_ran_iff (restrict_is_function f)] at yY,
  obtain ⟨x, xt, yx⟩ := yY, subst yx,
  have doms : R.rel.seg t ⊆ (eps_img_fun R).dom, rw dom, exact seg_sub_fld tf,
  rw restrict_dom doms at xt, rw restrict_fun_value f doms xt, rw dom at doms,
  have xA : x ∈ R.fld := doms xt,
  exact fun_value_mem_eps_img well xA,
end

structure isomorphism (R S : rel_struct) (f : Set) : Prop :=
(corr : R.fld.correspondence S.fld f)
(iso : ∀ ⦃x y : Set⦄, x ∈ R.fld → y ∈ R.fld → (x.pair y ∈ R.rel ↔ (f.fun_value x).pair (f.fun_value y) ∈ S.rel))

def isomorphic (R S : rel_struct) : Prop := ∃ f : Set, f.isomorphism R S

-- Theorem 7E part 1
theorem iso_refl {R : rel_struct} : isomorphic R R :=
begin
  use R.fld.id, split,
    exact ⟨id_onto, id_oto⟩,
  intros x y hx hy,
  rw [id_value hx, id_value hy],
end

-- Theorem 7E part 2
theorem iso_symm {R S : rel_struct} (h : isomorphic R S) : isomorphic S R :=
begin
  rcases h with ⟨f, corr, iso⟩,
  have hif : f.inv.is_function, rw T3F_a, exact corr.oto,
  have hio : f.inv.one_to_one, rw ←T3F_b corr.onto.left.left, exact corr.onto.left,
  use f.inv, split,
    exact corr_symm corr,
  intros X Y hX hY,
  rw ←corr.onto.right.right at hX hY,
  have hfX : f.inv.fun_value X ∈ R.fld, rw [←corr.onto.right.left, ←T3E_b],
    apply fun_value_def'' hif, rw T3E_a, exact hX,
  have hfY: f.inv.fun_value Y ∈ R.fld, rw [←corr.onto.right.left, ←T3E_b],
    apply fun_value_def'' hif, rw T3E_a, exact hY,
  rw [iso hfX hfY, T3G_b corr.onto.left corr.oto _ hX, T3G_b corr.onto.left corr.oto _ hY],
end

-- Theorem 7E part 3
theorem iso_trans {R S : rel_struct} (hRS : isomorphic R S) {T : rel_struct} (hST : isomorphic S T) : isomorphic R T :=
begin
  rcases hRS with ⟨f, fcorr, fiso⟩,
  rcases hST with ⟨g, gcorr, giso⟩,
  use g.comp f, split,
    exact corr_trans fcorr gcorr,
  intros x y hx hy,
  have hfx : f.fun_value x ∈ S.fld, rw ←fcorr.onto.right.right,
    apply fun_value_def'' fcorr.onto.left, rw fcorr.onto.right.left, exact hx,
  have hfy : f.fun_value y ∈ S.fld, rw ←fcorr.onto.right.right,
    apply fun_value_def'' fcorr.onto.left, rw fcorr.onto.right.left, exact hy,
  have gfd : (g.comp f).dom = f.dom, apply dom_comp,
    rw [fcorr.onto.right.right, gcorr.onto.right.left], exact subset_self,
  have hx' : x ∈ (g.comp f).dom, rw gfd, rw fcorr.onto.right.left, exact hx,
  have hy' : y ∈ (g.comp f).dom, rw gfd, rw fcorr.onto.right.left, exact hy,
  rw [T3H_c gcorr.onto.left fcorr.onto.left hx', T3H_c gcorr.onto.left fcorr.onto.left hy'],
  rw ←giso hfx hfy, rw ←fiso hx hy,
end

def fun_order (A R f : Set) : Set := pair_sep (λ x y, (f.fun_value x).pair (f.fun_value y) ∈ R) A A

-- Lemma 7F part a
lemma part_order_from_fun {A B f : Set} (into : f.into_fun A B) (oto : f.one_to_one)
  {R : Set} (rel : R ⊆ B.prod B) (part : R.part_order) :
  A.fun_order R f ⊆ A.prod A ∧ (A.fun_order R f).part_order :=
begin
  refine ⟨pair_sep_sub_prod, pair_sep_is_rel, _, _⟩,
    intros x y z xy yz, rw [fun_order, pair_mem_pair_sep] at *,
    rcases xy with ⟨xA, -, fxy⟩, rcases yz with ⟨-, zA, fyz⟩,
    exact ⟨xA, zA, part.trans fxy fyz⟩,
  intros x xx, rw [fun_order, pair_mem_pair_sep] at xx, exact part.irrefl xx.right.right,
end

-- Lemma 7F part b
lemma lin_order_from_fun {A B f : Set} (into : f.into_fun A B) (oto : f.one_to_one)
  {R : Set} (lin : B.lin_order R) : A.lin_order (A.fun_order R f) :=
begin
  have Bpart := part_order_of_lin_order lin,
  obtain ⟨rel, Apart⟩ := part_order_from_fun into oto lin.rel Bpart,
  refine ⟨rel, Apart.trans, Apart.irrefl, _⟩,
  intros x y xA yA xy, simp only [fun_order, pair_mem_pair_sep],
  have xd : x ∈ f.dom, rw into.right.left, exact xA,
  have yd : y ∈ f.dom, rw into.right.left, exact yA,
  have fx : f.fun_value x ∈ B, apply into.right.right,
    apply fun_value_def'' into.left, exact xd,
  have fy : f.fun_value y ∈ B, apply into.right.right,
    apply fun_value_def'' into.left, exact yd,
  have fxy : f.fun_value x ≠ f.fun_value y, intro fxy,
    exact xy (from_one_to_one into.left oto xd yd fxy),
  cases lin.conn fx fy fxy,
    left, exact ⟨xA, yA, h⟩,
  right, exact ⟨yA, xA, h⟩,
end

-- Lemma 7F part c
lemma well_order_from_fun {A B f : Set} (into : f.into_fun A B) (oto : f.one_to_one)
  {R : Set} (well : B.well_order R) : A.well_order (A.fun_order R f) :=
begin
  refine ⟨lin_order_from_fun into oto well.lin, _⟩,
  intros S SE SA,
  rw ←into.right.left at SA,
  have fSE : f.img S ≠ ∅, apply ne_empty_of_inhabited,
    replace SE := inhabited_of_ne_empty SE,
    cases SE with x xS, use f.fun_value x,
    apply fun_value_mem_img into.left SA xS,
  have fSB : f.img S ⊆ B := subset_trans img_subset_ran into.right.right,
  obtain ⟨M, MfS, le⟩ := well.well fSE fSB,
  rw mem_img' into.left SA at MfS, rcases MfS with ⟨m, mS, mM⟩, subst mM,
  refine ⟨m, mS, _⟩, rintro ⟨x, xS, xm⟩, apply le, rw [fun_order, pair_mem_pair_sep] at xm,
  refine ⟨f.fun_value x, fun_value_mem_img into.left SA xS, xm.right.right⟩,
end

lemma fun_order_eq {R S : rel_struct} {f : Set} (fiso : f.isomorphism S R) : S.fld.fun_order R.rel f = S.rel :=
begin
  apply rel_ext (pair_sep_is_rel) (sub_rel_is_rel prod_is_rel S.is_rel),
  intros x y, rw pair_mem_pair_sep, split,
    rintro ⟨hx, hy, fxy⟩, rw fiso.iso hx hy, exact fxy,
  intro xy,
  obtain ⟨hx, hy⟩ := mem_fld_of_pair_mem_rel_struct xy,
  rw ←fiso.iso hx hy, exact ⟨hx, hy, xy⟩,
end

-- Theorem 7G part a
theorem part_order_iso {R S : rel_struct} (RS : isomorphic R S) (part : R.rel.part_order) : S.rel.part_order :=
begin
  replace RS := iso_symm RS,
  cases RS with f fiso,
  have he := fun_order_eq fiso, rw ←he,
  exact (part_order_from_fun (into_of_onto fiso.corr.onto) fiso.corr.oto R.is_rel part).right,
end

-- Theorem 7G part b
theorem lin_order_iso {R S : rel_struct} (RS : isomorphic R S) (lin : R.fld.lin_order R.rel) : S.fld.lin_order S.rel :=
begin
  replace RS := iso_symm RS,
  cases RS with f fiso,
  have he := fun_order_eq fiso, rw ←he,
  exact (lin_order_from_fun (into_of_onto fiso.corr.onto) fiso.corr.oto lin),
end

-- Theorem 7G part c
theorem well_order_iso {R S : rel_struct} (RS : isomorphic R S) (well : R.fld.well_order R.rel) : S.fld.well_order S.rel :=
begin
  replace RS := iso_symm RS,
  cases RS with f fiso,
  have he := fun_order_eq fiso, rw ←he,
  exact (well_order_from_fun (into_of_onto fiso.corr.onto) fiso.corr.oto well),
end

def eps_order (A : Set) : Set := pair_sep (λ x y, x ∈ y) A A
def eps_order_rel_struct (A : Set) : rel_struct := ⟨A, A.eps_order, pair_sep_sub_prod⟩

@[simp]
lemma eps_order_rel_struct_fld {A : Set} : A.eps_order_rel_struct.fld = A := rfl
@[simp]
lemma eps_order_rel_struct_rel {A : Set} : A.eps_order_rel_struct.rel = A.eps_order := rfl

lemma pair_mem_eps_order {A x y : Set} (xA : x ∈ A) (yA : y ∈ A) : x.pair y ∈ A.eps_order_rel_struct.rel ↔ x ∈ y :=
begin
  simp only [eps_order_rel_struct_rel, eps_order, xA, yA, true_and, pair_mem_pair_sep],
end

lemma eps_img_iso {R : rel_struct} (well : R.fld.well_order R.rel) : (eps_img_fun R).isomorphism R (eps_img R).eps_order_rel_struct :=
begin
  refine ⟨⟨eps_img_fun_onto well, eps_img_fun_oto well⟩, _⟩,
  intros x y xA yA,
  have fx : (eps_img_fun R).fun_value x ∈ eps_img R := fun_value_mem_eps_img well xA,
  have fy : (eps_img_fun R).fun_value y ∈ eps_img R := fun_value_mem_eps_img well yA,
  rw [pair_mem_eps_order fx fy, fun_value_mem_eps_img_fun_iff well xA yA],
end

lemma eps_img_isomorphic {R : rel_struct} (well : R.fld.well_order R.rel) : isomorphic R (eps_img R).eps_order_rel_struct :=
⟨_, eps_img_iso well⟩

-- Corollary 7H
lemma eps_img_well_order {R : rel_struct} (well : R.fld.well_order R.rel) : (eps_img R).well_order (eps_img R).eps_order :=
well_order_iso (eps_img_isomorphic well) well

-- Exercise 13
theorem iso_unique {R S : rel_struct} (Rwell : R.fld.well_order R.rel) (Swell : S.fld.well_order S.rel) (iso : isomorphic R S) :
  ∃! f : Set, f.isomorphism R S :=
begin
  apply exists_unique_of_exists_of_unique iso, intros f g fiso giso,
  apply fun_ext fiso.corr.onto.left giso.corr.onto.left,
    rw [fiso.corr.onto.right.left, giso.corr.onto.right.left],
  intros y yA, rw fiso.corr.onto.right.left at yA, apply classical.by_contradiction, intro fg,
  let X := {x ∈ R.fld | f.fun_value x ≠ g.fun_value x},
  have XA : X ⊆ R.fld := sep_subset,
  have XE : X ≠ ∅, apply ne_empty_of_inhabited, use y, rw mem_sep, exact ⟨yA, fg⟩,
  obtain ⟨m, mA, le⟩ := Rwell.well XE XA, apply le,
  rw mem_sep at mA,
  have fm : f.fun_value m ∈ S.fld, rw ←fiso.corr.onto.right.right,
    apply fun_value_def'' fiso.corr.onto.left, rw fiso.corr.onto.right.left, exact mA.left,
  have gm : g.fun_value m ∈ S.fld, rw ←giso.corr.onto.right.right,
    apply fun_value_def'' giso.corr.onto.left, rw giso.corr.onto.right.left, exact mA.left,
  cases Swell.lin.conn fm gm mA.right with fgm gfm,
    rw [←giso.corr.onto.right.right, mem_ran_iff giso.corr.onto.left] at fm,
    rcases fm with ⟨x, xA, mx⟩, rw mx at fgm, rw giso.corr.onto.right.left at xA,
    rw ←giso.iso xA mA.left at fgm, refine ⟨x, _, fgm⟩, rw mem_sep, refine ⟨xA, _⟩,
    rw ←mx, intro fxm,
    rw ←fiso.corr.onto.right.left at xA mA,
    have xem : x = m := from_one_to_one fiso.corr.onto.left fiso.corr.oto xA mA.left fxm, subst xem,
    exact Rwell.lin.irrefl fgm,
  rw [←fiso.corr.onto.right.right, mem_ran_iff fiso.corr.onto.left] at gm,
  rcases gm with ⟨x, xA, mx⟩, rw mx at gfm, rw fiso.corr.onto.right.left at xA,
  rw ←fiso.iso xA mA.left at gfm, refine ⟨x, _, gfm⟩, rw mem_sep, refine ⟨xA, _⟩,
  rw ←mx, intro gmx,
  rw ←giso.corr.onto.right.left at xA mA,
  have mex : m = x := from_one_to_one giso.corr.onto.left giso.corr.oto mA.left xA gmx, subst mex,
  exact Rwell.lin.irrefl gfm,
end

-- Theorem 7I
theorem iso_iff_eps_img_eq {R S : rel_struct} (Rwell : R.fld.well_order R.rel) (Swell : S.fld.well_order S.rel) :
  isomorphic R S ↔ eps_img R = eps_img S :=
begin
  split,
    rintro ⟨f, ⟨fonto, foto⟩, fiso⟩,
    obtain ⟨⟨Ronto, Roto⟩, Riso⟩ := eps_img_iso Rwell,
    obtain ⟨⟨Sonto, Soto⟩, Siso⟩ := eps_img_iso Swell,
    let E₁ := eps_img_fun R, let E₂ := eps_img_fun S,
    let B := {s ∈ R.fld | E₁.fun_value s = E₂.fun_value (f.fun_value s)},
    suffices hBA : B = R.fld, apply ext, intro x, rw [mem_eps_img Rwell, mem_eps_img Swell], split,
        rintro ⟨s, sA, xfs⟩, rw [←hBA, mem_sep] at sA, rw sA.right at xfs, refine ⟨_, _, xfs⟩,
        rw ←fonto.right.right, apply fun_value_def'' fonto.left, rw fonto.right.left, exact sA.left,
      rintro ⟨t, tA, xft⟩, subst xft,
      rw [←fonto.right.right, mem_ran_iff fonto.left] at tA,
      obtain ⟨s, sA, tfs⟩ := tA, subst tfs, rw [fonto.right.left, ←hBA, mem_sep] at sA,
      rw ←sA.right, exact ⟨_, sA.left, rfl⟩,
    apply transfinite_ind Rwell sep_subset, intros s sA sub, rw mem_sep, refine ⟨sA, _⟩,
    apply ext, intro z,
    have fs : f.fun_value s ∈ S.fld, rw ←fonto.right.right, apply fun_value_def'' fonto.left, rw fonto.right.left, exact sA,
    rw [mem_eps_img_fun Rwell sA, mem_eps_img_fun Swell fs], split,
      rintro ⟨x, xs, zfx⟩, subst zfx, use f.fun_value x, split,
        rw ←fiso (mem_fld_of_pair_mem_rel_struct xs).left sA, exact xs,
      rw ←mem_seg at xs, replace xs := sub xs, rw mem_sep at xs, exact xs.right,
    rintro ⟨y, yfs, zfy⟩, subst zfy,
    have yr : y ∈ f.ran, rw fonto.right.right, exact (mem_fld_of_pair_mem_rel_struct yfs).left,
    rw mem_ran_iff fonto.left at yr, obtain ⟨x, xA, yfs⟩ := yr, subst yfs, use x,
    rw fonto.right.left at xA, rw ←fiso xA sA at yfs, split,
      exact yfs,
    symmetry, rw ←mem_seg at yfs, replace yfs := sub yfs, rw mem_sep at yfs, exact yfs.right,
  intro he, apply iso_trans (eps_img_isomorphic Rwell), rw he, exact iso_symm (eps_img_isomorphic Swell),
end

def is_ordinal (S : Set) : Prop := ∃ R : rel_struct, R.fld.well_order R.rel ∧ S = eps_img R
def rel_struct_restrict (R : rel_struct) (S : Set) : rel_struct := ⟨S, R.rel ∩ (S.prod S), inter_subset_right⟩

@[simp]
lemma rel_struct_restrict_fld {R : rel_struct} {S : Set} : (S.rel_struct_restrict R).fld = S := rfl
@[simp]
lemma rel_struct_restrict_rel {R : rel_struct} {S : Set} : (S.rel_struct_restrict R).rel = R.rel ∩ (S.prod S) := rfl

def part_order_on (A R : Set) : Prop := R.part_order ∧ R ⊆ A.prod A

lemma part_from_lin {A R : Set} (lin : A.lin_order R) : A.part_order_on R := ⟨part_order_of_lin_order lin, lin.rel⟩

lemma part_to_lin {A R : Set} (part : A.part_order_on R) (conn : ∀ ⦃x y : Set⦄, x ∈ A → y ∈ A → x ≠ y → x.pair y ∈ R ∨ y.pair x ∈ R) :
  A.lin_order R := ⟨part.right, part.left.trans, part.left.irrefl, conn⟩

-- Theorem 7J part a
theorem part_order_rel_struct_restrict {R : rel_struct} (Rpart : R.fld.part_order_on R.rel) {S : Set} (SR : S ⊆ R.fld) :
  (S.rel_struct_restrict R).fld.part_order_on (S.rel_struct_restrict R).rel :=
begin
  simp, refine ⟨⟨inter_rel_is_rel Rpart.left.rel, _, _⟩, inter_subset_right⟩,
  { intros x y z xy yz, rw [mem_inter, pair_mem_prod] at *,
    exact ⟨Rpart.left.trans xy.left yz.left, xy.right.left, yz.right.right⟩, },
  { intros x xx, rw mem_inter at xx, exact Rpart.left.irrefl xx.left, },
end 

-- Theorem 7J part b
theorem lin_order_rel_struct_restrict {R : rel_struct} (Rlin : R.fld.lin_order R.rel) {S : Set} (SR : S ⊆ R.fld) :
  (S.rel_struct_restrict R).fld.lin_order (S.rel_struct_restrict R).rel :=
begin
  apply part_to_lin (part_order_rel_struct_restrict (part_from_lin Rlin) SR), simp,
  intros x y xS yS xy, cases Rlin.conn (SR xS) (SR yS) xy with xly ylx,
    exact or.inl ⟨xly, xS, yS⟩,
  exact or.inr ⟨ylx, yS, xS⟩,
end

-- Theorem 7J part c
theorem well_order_rel_struct_restrict {R : rel_struct} (Rwell : R.fld.well_order R.rel) {S : Set} (SR : S ⊆ R.fld) :
  (S.rel_struct_restrict R).fld.well_order (S.rel_struct_restrict R).rel :=
begin
  refine ⟨lin_order_rel_struct_restrict Rwell.lin SR, _⟩, simp,
  intros X XE XS,
  obtain ⟨m, mX, le⟩ := Rwell.well XE (subset_trans XS SR),
  refine ⟨_, mX, _⟩, rintro ⟨x, xX, xm⟩, rw mem_inter at xm, exact le ⟨_, xX, xm.left⟩,
end

-- Theorem 7K
theorem T7K {R : rel_struct.{u}} (Rwell : R.fld.well_order R.rel) {S : rel_struct.{u}} (Swell : S.fld.well_order S.rel) :
  isomorphic R S
  ∨ (∃ b : Set, b ∈ S.fld ∧ isomorphic R ((S.rel.seg b).rel_struct_restrict S))
  ∨ (∃ a : Set, a ∈ R.fld ∧ isomorphic ((R.rel.seg a).rel_struct_restrict R) S) :=
begin
  let e : Set := classical.some (univ_not_set' (R.fld ∪ S.fld)),
  have eRS : e ∉ R.fld ∪ S.fld := classical.some_spec (univ_not_set' (R.fld ∪ S.fld)),
  rw mem_union at eRS, push_neg at eRS,
  let g : Set → Set := λ f, if case : ∃ m, m ∈ (S.fld \ f.ran) ∧ (S.fld \ f.ran).is_least S.rel m
    then classical.some case else e,
  have gt : ∀ {f : Set}, (∃ m, m ∈ (S.fld \ f.ran) ∧ (S.fld \ f.ran).is_least S.rel m)
    → (g f) ∈ (S.fld \ f.ran) ∧ (S.fld \ f.ran).is_least S.rel (g f),
    intros f case, dsimp only [g], rw [dif_pos case], exact classical.some_spec case,
  have gf : ∀ {f : Set}, ¬ (∃ m, m ∈ (S.fld \ f.ran) ∧ (S.fld \ f.ran).is_least S.rel m) → g f = e,
    intros f case, dsimp only [g], rw [dif_neg case],
  have ge : ∀ {f : Set}, g f = e → S.fld \ f.ran = ∅, intros f gf,
    apply classical.by_contradiction, intro ne,
    obtain ⟨m, hm, mle⟩ := Swell.well ne subset_diff,
    obtain ⟨hgf, gfle⟩ := gt ⟨_, hm, mle⟩,
    rw least_unique Swell.lin subset_diff hgf hm gfle mle at gf,
    apply eRS.right, rw mem_diff at hm, rw ←gf, exact hm.left,
  obtain ⟨F, Ffun, Fdom, Fval⟩ := exists_of_exists_unique (transfinite_rec' Rwell g),
  have Fxle : ∀ {x : Set}, x ∈ R.fld → F.fun_value x ≠ e → (S.fld \ F.img (R.rel.seg x)).is_least S.rel (F.fun_value x),
    intros x xA Fxne,
    have ex : ∃ m, m ∈ (S.fld \ F.img (R.rel.seg x)) ∧ (S.fld \ F.img (R.rel.seg x)).is_least S.rel m,
      apply classical.by_contradiction, intro nem, rw Fval xA at Fxne, exact Fxne (gf nem),
    rw Fval xA, exact (gt ex).right,
  have Fran : F.ran ⊆ S.fld ∪ {e}, intros y yF, rw mem_ran_iff Ffun at yF, obtain ⟨x, xA, yFx⟩ := yF,
    rw Fdom at xA, rw Fval xA at yFx, rw [mem_union, mem_singleton], subst yFx,
    by_cases case : ∃ m, m ∈ (S.fld \ (F.restrict (R.rel.seg x)).ran) ∧ (S.fld \ (F.restrict (R.rel.seg x)).ran).is_least S.rel m,
      have h := (gt case).left, rw mem_diff at h, left, exact h.left,
    right, exact gf case,
  have seg_sub_dom : ∀ {y : Set}, y ∈ R.fld → R.rel.seg y ⊆ F.dom, intros y yA, rw Fdom, exact seg_sub_fld yA,
  have seg_sub_dom' : ∀ {x y : Set}, x.pair y ∈ R.rel → R.rel.seg y ⊆ F.dom, intros x y xy,
    exact seg_sub_dom (mem_fld_of_pair_mem_rel_struct xy).right,
  have sub_of_le : ∀ {x y : Set}, R.rel.lin_le x y → S.fld \ F.img (R.rel.seg y) ⊆ S.fld \ F.img (R.rel.seg x),
    intros x y xy, cases xy,
      obtain ⟨xA, yA⟩ := mem_fld_of_pair_mem_rel_struct xy,
      apply diff_sub_diff_of_sub, intros Z hZ,
      rw mem_img' Ffun (seg_sub_dom xA) at hZ, obtain ⟨z, zx, hZ⟩ := hZ, subst hZ,
      apply fun_value_mem_img Ffun (seg_sub_dom yA), exact (seg_subset_seg Rwell.lin xy) zx,
    subst xy, exact subset_self,
  have Fle_of_le : ∀ {x y : Set}, R.rel.lin_le x y → F.fun_value x ≠ e → F.fun_value y ≠ e → S.rel.lin_le (F.fun_value x) (F.fun_value y),
    intros x y xy Fxne Fyne, cases xy with xly xey,
      obtain ⟨xA, yA⟩ := mem_fld_of_pair_mem_rel_struct xly,
      have sub := sub_of_le (or.inl xly),
      have ex : ∃ m, m ∈ (S.fld \ F.img (R.rel.seg x)) ∧ (S.fld \ F.img (R.rel.seg x)).is_least S.rel m,
        apply classical.by_contradiction, intro nem, rw Fval xA at Fxne, exact Fxne (gf nem),
      have ey : ∃ m, m ∈ (S.fld \ F.img (R.rel.seg y)) ∧ (S.fld \ F.img (R.rel.seg y)).is_least S.rel m,
        apply classical.by_contradiction, intro nem, rw Fval yA at Fyne, exact Fyne (gf nem),
      have Fxle := (gt ex).right, have Fym := (gt ey).left,
      rw ←Fval xA at Fxle, rw ←Fval yA at Fym,
      have FxB : F.fun_value x ∈ S.fld ∪ {e}, apply Fran, apply fun_value_def'' Ffun, rw Fdom, exact xA,
      have FyB : F.fun_value y ∈ S.fld ∪ {e}, apply Fran, apply fun_value_def'' Ffun, rw Fdom, exact yA,
      rw [mem_union, mem_singleton] at FxB FyB,
      cases FxB with FxB Fxe,
        cases FyB with FyB Fye,
          rw le_iff_not_lt Swell.lin FxB FyB, intro Fyx, apply Fxle, exact ⟨_, sub Fym, Fyx⟩,
        exfalso, exact Fyne Fye,
      exfalso, exact Fxne Fxe,
    subst xey, right, refl,
  have Fx_in_Fy : ∀ {x y : Set}, x.pair y ∈ R.rel → F.fun_value x ∈ F.img (R.rel.seg y), intros x y xy,
    apply fun_value_mem_img Ffun (seg_sub_dom' xy), rw mem_seg, exact xy,
  have Fx_nin_Fx : ∀ {x : Set}, x ∈ R.fld → F.fun_value x ≠ e → F.fun_value x ∉ F.img (R.rel.seg x),
    intros x xA Fxe,
    have em : ∃ m, m ∈ (S.fld \ F.img (R.rel.seg x)) ∧ (S.fld \ F.img (R.rel.seg x)).is_least S.rel m,
      apply classical.by_contradiction, intro nem, rw Fval xA at Fxe, exact Fxe (gf nem),
    have h := (gt em).left, rw [mem_diff, ←Fval xA] at h, exact h.right,
  have Fne_of_ne : ∀ {x y : Set}, x ∈ R.fld → y ∈ R.fld → x ≠ y → F.fun_value x ≠ e → F.fun_value y ≠ e → F.fun_value x ≠ F.fun_value y,
    intros x y xA yA xy Fxe Fye Fxy, cases Rwell.lin.conn xA yA xy with xly ylx,
      specialize Fx_in_Fy xly, rw Fxy at Fx_in_Fy, exact Fx_nin_Fx yA Fye Fx_in_Fy,
    specialize Fx_in_Fy ylx, rw ←Fxy at Fx_in_Fy, exact Fx_nin_Fx xA Fxe Fx_in_Fy,
  have Flt_of_lt : ∀ {x y : Set}, x.pair y ∈ R.rel → F.fun_value x ≠ e → F.fun_value y ≠ e → (F.fun_value x).pair (F.fun_value y) ∈ S.rel,
    intros x y xy Fxe Fye,
    have xny : x ≠ y, intro xey, subst xey, exact Rwell.lin.irrefl xy,
    cases Fle_of_le (or.inl xy) Fxe Fye with lt eq,
      exact lt,
    have xA := (mem_fld_of_pair_mem_rel_struct xy).left, have yA := (mem_fld_of_pair_mem_rel_struct xy).right,
    exfalso, exact Fne_of_ne xA yA xny Fxe Fye eq,
  have lt_of_Flt : ∀ {x y : Set}, x ∈ R.fld → y ∈ R.fld → (F.fun_value x).pair (F.fun_value y) ∈ S.rel
    → F.fun_value x ≠ e → F.fun_value y ≠ e → x.pair y ∈ R.rel,
    intros x y xA yA Fxy Fxne Fyne,
    have FxB : F.fun_value x ∈ S.fld,
      have h : F.fun_value x ∈ S.fld ∪ {e}, apply Fran, rw ←Fdom at xA, exact fun_value_def'' Ffun xA,
      rw [mem_union, mem_singleton] at h, cases h with FxB Fxe,
        exact FxB,
      exfalso, exact Fxne Fxe,
    have FyB : F.fun_value y ∈ S.fld,
      have h : F.fun_value y ∈ S.fld ∪ {e}, apply Fran, rw ←Fdom at yA, exact fun_value_def'' Ffun yA,
      rw [mem_union, mem_singleton] at h, cases h with FyB Fye,
        exact FyB,
      exfalso, exact Fyne Fye,
    rw lt_iff_not_le Swell.lin FxB FyB at Fxy, rw lt_iff_not_le Rwell.lin xA yA,
    intro ylex, exact Fxy (Fle_of_le ylex Fyne Fxne),
  by_cases case₁ : e ∈ F.ran,
    let C := {x ∈ R.fld | F.fun_value x = e},
    have CE : C ≠ ∅, apply ne_empty_of_inhabited, rw mem_ran_iff Ffun at case₁,
      obtain ⟨x, xA, ee⟩ := case₁, use x, rw mem_sep, rw Fdom at xA, exact ⟨xA, ee.symm⟩,
    obtain ⟨a, aA, le⟩ := Rwell.well CE sep_subset, rw [mem_sep] at aA, obtain ⟨aA, Fa⟩ := aA,
    rw Fval aA at Fa,
    let F' := F.restrict (R.rel.seg a),
    have Fran : F'.ran = S.fld, rw eq_iff_subset_and_subset, split,
        intros y yF, simp only [restrict_ran, mem_img' Ffun (seg_sub_dom aA), mem_seg] at yF,
        obtain ⟨x, xa, yFx⟩ := yF, subst yFx,
        have xA : x ∈ R.fld := (mem_fld_of_pair_mem_rel_struct xa).left,
        have gF : (F.restrict (R.rel.seg a)).fun_value x ∈ S.fld ∪ {e}, apply Fran,
          rw ←mem_seg at xa, rw restrict_fun_value Ffun (seg_sub_dom aA) xa,
          rw ←Fdom at xA, exact fun_value_def'' Ffun xA,
        have xsa : x ∈ R.rel.seg a, rw mem_seg, exact xa,
        rw [restrict_fun_value Ffun (seg_sub_dom aA) xsa, mem_union, mem_singleton] at gF, cases gF,
          exact gF,
        exfalso, apply le, refine ⟨x, _, xa⟩, rw mem_sep, exact ⟨xA, gF⟩,
      intros y yB, apply classical.by_contradiction, intro yF, apply mem_empty y,
      rw ←ge Fa, rw mem_diff, exact ⟨yB, yF⟩,
    have fne : ∀ {x : Set}, x.pair a ∈ R.rel → F.fun_value x ≠ e, intros x xa Fxe,
      apply le, refine ⟨_, _, xa⟩, rw mem_sep, exact ⟨(mem_fld_of_pair_mem_rel_struct xa).left, Fxe⟩,
    have Foto : F'.one_to_one, apply one_to_one_of (restrict_is_function Ffun), intros x xa y ya xy,
      rw restrict_dom (seg_sub_dom aA) at xa ya,
      rw [restrict_fun_value Ffun (seg_sub_dom aA) xa, restrict_fun_value Ffun (seg_sub_dom aA) ya],
      rw mem_seg at xa ya,
      have xA := (mem_fld_of_pair_mem_rel_struct xa).left, have yA := (mem_fld_of_pair_mem_rel_struct ya).left,
      exact Fne_of_ne xA yA xy (fne xa) (fne ya),
    right, right, refine ⟨_, aA, F', ⟨⟨⟨restrict_is_function Ffun, restrict_dom (seg_sub_dom aA), Fran⟩, Foto⟩, _⟩⟩,
    intros x y xa ya, rw rel_struct_restrict_fld at xa ya,
    simp only [rel_struct_restrict_rel, mem_inter, pair_mem_prod],
    rw [restrict_fun_value Ffun (seg_sub_dom aA) xa, restrict_fun_value Ffun (seg_sub_dom aA) ya],
    rw mem_seg at xa ya,
    have xA : x ∈ R.fld := (mem_fld_of_pair_mem_rel_struct xa).left,
    have yA : y ∈ R.fld := (mem_fld_of_pair_mem_rel_struct ya).left,
    split,
      rintro ⟨xy, -, -⟩, exact Flt_of_lt xy (fne xa) (fne ya),
    intro Fxy, simp only [mem_seg], exact ⟨lt_of_Flt xA yA Fxy (fne xa) (fne ya), xa, ya⟩,
  have fne : ∀ {x : Set}, x ∈ R.fld → F.fun_value x ≠ e, intros x xA Fxe,
    apply case₁, rw ←Fxe, apply fun_value_def'' Ffun, rw Fdom, exact xA,
  have Foto : F.one_to_one, apply one_to_one_of Ffun, intros x xA y yA xy,
    rw Fdom at xA yA, exact Fne_of_ne xA yA xy (fne xA) (fne yA),
  have Fran' : F.ran ⊆ S.fld, intros y yF,
    have h : y ∈ S.fld ∪ {e} := Fran yF,
    rw [mem_union, mem_singleton] at h, cases h with yB ye,
      exact yB,
    exfalso, rw ye at yF, exact case₁ yF,
  by_cases case₂ : F.ran = S.fld,
    left, refine ⟨_, ⟨⟨Ffun, Fdom, case₂⟩, Foto⟩, _⟩, intros x y xA yA, split,
      intro xy, exact Flt_of_lt xy (fne xA) (fne yA),
    intro Fxy, exact lt_of_Flt xA yA Fxy (fne xA) (fne yA),
  have ne : S.fld \ F.ran ≠ ∅,
    have nsub : ¬ S.fld ⊆ F.ran, intro h, apply case₂, rw eq_iff_subset_and_subset, exact ⟨Fran', h⟩,
    intro eqz, rw eq_empty at eqz, apply nsub, intros y yB, apply classical.by_contradiction, intro ynF,
    apply eqz y, rw mem_diff, exact ⟨yB, ynF⟩,
  obtain ⟨b, bBF, le⟩ := Swell.well ne subset_diff, rw mem_diff at bBF,
  have Fran : F.ran = S.rel.seg b, rw eq_iff_subset_and_subset, split,
      intros y yF, rw mem_ran_iff Ffun at yF, obtain ⟨x, xA, yFx⟩ := yF, rw Fdom at xA, subst yFx,
      have FxB : F.fun_value x ∈ S.fld,
        have Fxran : F.fun_value x ∈ S.fld ∪ {e}, apply Fran, apply fun_value_def'' Ffun, rw Fdom, exact xA,
        rw [mem_union, mem_singleton] at Fxran, cases Fxran with FxB Fxe,
          exact FxB,
        exfalso, exact (fne xA) Fxe,
      rw [mem_seg, lt_iff_not_le Swell.lin FxB bBF.left], rintro (bFx|eq),
        apply Fxle xA (fne xA), refine ⟨_, _, bFx⟩, rw mem_diff, refine ⟨bBF.left, _⟩,
        intro mem_img, exact bBF.right (img_subset_ran mem_img),
      subst eq, apply bBF.right, rw ←Fdom at xA, exact fun_value_def'' Ffun xA,
    intros x xb, rw mem_seg at xb, apply classical.by_contradiction, intro xF, apply le, refine ⟨_, _, xb⟩,
    rw mem_diff, exact ⟨(mem_fld_of_pair_mem_rel_struct xb).left, xF⟩,
  right, left, refine ⟨_, bBF.left, F, ⟨⟨⟨Ffun, Fdom, Fran⟩, Foto⟩, _⟩⟩,
  intros x y xA yA, simp only [←Fran, rel_struct_restrict_rel, mem_inter, pair_mem_prod], split,
    intro xy, refine ⟨Flt_of_lt xy (fne xA) (fne yA), fun_value_def'' Ffun _, fun_value_def'' Ffun _⟩,
      rw Fdom, exact xA,
    rw Fdom, exact yA,
  rintro ⟨Fxy, -, -⟩, exact lt_of_Flt xA yA Fxy (fne xA) (fne yA),
end

def eps_ordered (A : Set) : Prop := A.well_order A.eps_order

lemma seg_eq_of_trans {A : Set} (trans : A.transitive_set) {t : Set} (tA : t ∈ A) : A.eps_order.seg t = t :=
begin
  apply ext, intro x, rw [mem_seg, eps_order, pair_mem_pair_sep], split,
    rintro ⟨-, -, xt⟩, exact xt,
  intro xt, refine ⟨_, tA, xt⟩, apply trans, rw mem_Union, exact ⟨_, tA, xt⟩,
end

-- Theorem 7L
theorem eps_img_trans_well_eq_self {α : Set} (trans : α.transitive_set) (well : α.well_order α.eps_order) : eps_img α.eps_order_rel_struct = α :=
begin
  have well' : α.eps_order_rel_struct.fld.well_order α.eps_order_rel_struct.rel,
    simp only [eps_order_rel_struct_rel, eps_order_rel_struct_fld], exact well,
  obtain ⟨efun, edom, eran⟩ := eps_img_fun_onto well',
  let B := {x ∈ α | (eps_img_fun α.eps_order_rel_struct).fun_value x = x},
  have Be : B = α, apply transfinite_ind well sep_subset, intros t tA ind,
    have tA' : t ∈ α.eps_order_rel_struct.fld, exact tA,
    rw [mem_sep, eps_img_fun_value_img well' tA', eps_order_rel_struct_rel],
    refine ⟨tA, _⟩, apply ext, intro y,
    have seg_sub : α.eps_order.seg t ⊆ α.eps_order_rel_struct.fld, rw [eps_order_rel_struct_fld], exact subset_trans ind sep_subset,
    rw ←edom at seg_sub, rw [mem_img' efun seg_sub], split,
      rintro ⟨x, xt, yx⟩, subst yx, specialize ind xt, rw mem_sep at ind, rw ind.right,
      rw [mem_seg, eps_order, pair_mem_pair_sep] at xt, exact xt.right.right,
    intro yt,
    have yt' : y ∈ α.eps_order.seg t, rw [mem_seg, eps_order, pair_mem_pair_sep], refine ⟨_, tA, yt⟩,
      apply trans, rw mem_Union, exact ⟨_, tA, yt⟩,
    specialize ind yt', rw mem_sep at ind, refine ⟨_, yt', ind.right.symm⟩,
  have ef : eps_img_fun α.eps_order_rel_struct = α.id, apply fun_ext efun id_is_function,
      simp only [edom, id_into.right.left, eps_order_rel_struct_fld],
    intros t tA, rw [edom, eps_order_rel_struct_fld, ←Be, mem_sep] at tA,
    rw [id_value tA.left, tA.right],
  rw [←eran, ef], nth_rewrite 1 [←(@id_onto α).right.right],
end

theorem eps_img_trans_well_is_ordinal {α : Set} (trans : α.transitive_set) (well : α.well_order α.eps_order) : α.is_ordinal :=
⟨α.eps_order_rel_struct, well, (eps_img_trans_well_eq_self trans well).symm⟩

lemma ordinal_well_ordered {α : Set} (ordinal : α.is_ordinal) : α.well_order α.eps_order :=
begin
  rcases ordinal with ⟨R, well, Re⟩, rw Re, exact eps_img_well_order well,
end

lemma ordinal_trans {α : Set} (ordinal : α.is_ordinal) : α.transitive_set :=
begin
  rcases ordinal with ⟨R, well, Re⟩, rw Re, exact eps_img_transitive well,
end

lemma restrict_seg_sub {R : rel_struct} {t : Set} (tA : t ∈ R.fld) : (rel_struct_restrict R (R.rel.seg t)).rel.seg t ⊆ R.rel.seg t :=
begin
  intro x, simp only [mem_seg, rel_struct_restrict_rel, mem_inter],rintro ⟨xt, -⟩, exact xt,
end

lemma eps_img_fun_restrict {R : rel_struct} (well : R.fld.well_order R.rel) {T : Set} (TA : T ∈ R.fld) :
  ∀ {x : Set}, x ∈ R.rel.seg T → (eps_img_fun (rel_struct_restrict R (R.rel.seg T))).fun_value x = (eps_img_fun R).fun_value x :=
begin
  have sub := seg_sub_fld TA,
  have well' := well_order_rel_struct_restrict well sub,
  obtain ⟨efun, edom, -⟩ := eps_img_fun_onto well,
  obtain ⟨efun', edom', -⟩ := eps_img_fun_onto well',
  let B := {x ∈ R.rel.seg T | (eps_img_fun (rel_struct_restrict R (R.rel.seg T))).fun_value x = (eps_img_fun R).fun_value x},
  have BA : B = R.rel.seg T, apply transfinite_ind well' sep_subset,
    intros t ht ind, rw mem_sep, refine ⟨ht, _⟩,
    rw [eps_img_fun_value_img well' ht, eps_img_fun_value_img well (sub ht)], apply ext, intro x,
    have dsub : R.rel.seg t ⊆ (eps_img_fun R).dom, rw edom, exact seg_sub_fld (sub ht),
    have dsub' : (rel_struct_restrict R (R.rel.seg T)).rel.seg t ⊆ (eps_img_fun (rel_struct_restrict R (R.rel.seg T))).dom,
      rw [edom', rel_struct_restrict_rel, rel_struct_restrict_fld], intro z,
      simp only [mem_seg, mem_inter, pair_mem_prod], rintro ⟨-, zT, -⟩, exact zT,
    rw [mem_img' efun dsub, mem_img' efun' dsub'], split,
      rintro ⟨z, zt, xz⟩, subst xz, specialize ind zt, rw mem_sep at ind,
      rw [rel_struct_restrict_rel, mem_seg, mem_inter, ←mem_seg] at zt, exact ⟨_, zt.left, ind.right⟩,
    rintro ⟨z, zt, xz⟩, subst xz, use z,
    have zt' : z ∈ (rel_struct_restrict R (R.rel.seg T)).rel.seg t,
      simp only [mem_seg, rel_struct_restrict_rel, mem_inter, mem_prod, exists_prop],
      rw [rel_struct_restrict_fld] at ht, rw mem_seg at zt ht,
      exact ⟨zt, _, well.lin.trans zt ht, _, ht, rfl⟩,
    specialize ind zt', rw mem_sep at ind, exact ⟨zt', ind.right.symm⟩,
  intros t tT, rw [←BA, mem_sep] at tT, exact tT.right,
end

lemma eps_img_img_eps_fun {R : rel_struct} (well : R.fld.well_order R.rel) {t : Set} (tA : t ∈ R.fld) :
  eps_img ((R.rel.seg t).rel_struct_restrict R) = (eps_img_fun R).img (R.rel.seg t) :=
begin
  have well' : (rel_struct_restrict R (R.rel.seg t)).fld.well_order (rel_struct_restrict R (R.rel.seg t)).rel
    := well_order_rel_struct_restrict well (seg_sub_fld tA),
  obtain ⟨efun, edom, -⟩ := eps_img_fun_onto well,
  have sub : R.rel.seg t ⊆ (eps_img_fun R).dom, rw edom, exact seg_sub_fld tA,
  apply ext, simp only [mem_eps_img well', mem_img' efun sub, rel_struct_restrict_fld], intro y, split,
    rintro ⟨x, xt, yx⟩, subst yx, refine ⟨x, xt, eps_img_fun_restrict well tA xt⟩,
  rintro ⟨x, xt, yx⟩, subst yx, refine ⟨x, xt, (eps_img_fun_restrict well tA xt).symm⟩,
end

-- Theorem 7M part a
theorem ord_of_mem_ord {α : Set} (ord : α.is_ordinal) {x : Set} (xα : x ∈ α) : x.is_ordinal :=
begin
  rcases ord with ⟨R, well, αe⟩, rw [αe, mem_eps_img well] at xα,
  obtain ⟨t, tA, xt⟩ := xα, subst xt,
  refine ⟨(R.rel.seg t).rel_struct_restrict R, well_order_rel_struct_restrict well (seg_sub_fld tA), _⟩,
  rw [eps_img_fun_value_img well tA], exact (eps_img_img_eps_fun well tA).symm,
end

-- Theorem 7M part b
theorem ord_mem_trans {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) {γ : Set} (γord : γ.is_ordinal)
  (αβ : α ∈ β) (βγ : β ∈ γ) : α ∈ γ :=
transitive_set_iff.mp (ordinal_trans γord) βγ αβ

-- Theorem 7M part c
theorem ord_mem_irrefl {α : Set} (ordinal : α.is_ordinal) : α ∉ α :=
begin
  rcases ordinal with ⟨R, well, αe⟩, subst αe, intro ee,
  obtain ⟨t, tA, ee'⟩ := (mem_eps_img well).mp ee, rw ee' at ee,
  exact eps_img_fun_irrefl well tA ee,
end

lemma restrict_eps_order_eq {β : Set} (βtrans : β.transitive_set) {δ : Set} (δβ : δ ∈ β) : rel_struct_restrict β.eps_order_rel_struct δ = δ.eps_order_rel_struct :=
begin
  simp only [eps_order_rel_struct, rel_struct_restrict, eps_order], refine ⟨rfl, _⟩,
  apply rel_ext (inter_rel_is_rel pair_sep_is_rel) pair_sep_is_rel, intros x y,
  simp only [mem_inter, pair_mem_pair_sep, pair_mem_prod], split,
    rintro ⟨⟨-, -, xy⟩, xδ, yδ⟩, exact ⟨xδ, yδ, xy⟩,
  rw transitive_set_iff at βtrans,
  rintro ⟨xδ, yδ, xy⟩, exact ⟨⟨βtrans δβ xδ, βtrans δβ yδ, xy⟩, xδ, yδ⟩,
end

lemma mem_of_iso_seg {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) {δ : Set} (δβ : δ ∈ β)
  (iso : isomorphic α.eps_order_rel_struct (rel_struct_restrict β.eps_order_rel_struct (β.eps_order_rel_struct.rel.seg δ))) : α ∈ β :=
begin
  have αwell : α.eps_order_rel_struct.fld.well_order α.eps_order_rel_struct.rel := ordinal_well_ordered αord,
  have βwell : β.eps_order_rel_struct.fld.well_order β.eps_order_rel_struct.rel := ordinal_well_ordered βord,
  have αtrans := ordinal_trans αord, have βtrans := ordinal_trans βord,
  rw [eps_order_rel_struct_rel, seg_eq_of_trans βtrans δβ, restrict_eps_order_eq βtrans δβ] at iso,
  have δord := ord_of_mem_ord βord δβ,
  have δwell : δ.eps_order_rel_struct.fld.well_order δ.eps_order_rel_struct.rel := ordinal_well_ordered δord,
  have δtrans := ordinal_trans δord,
  rw [iso_iff_eps_img_eq αwell δwell] at iso,
  rw [eps_img_trans_well_eq_self αtrans αwell, eps_img_trans_well_eq_self δtrans δwell] at iso,
  subst iso, exact δβ,
end

-- Theorem 7M part d
theorem ord_conn {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) (αβ : α ≠ β) : α ∈ β ∨ β ∈ α :=
begin
  have αwell : α.eps_order_rel_struct.fld.well_order α.eps_order_rel_struct.rel := ordinal_well_ordered αord,
  have βwell : β.eps_order_rel_struct.fld.well_order β.eps_order_rel_struct.rel := ordinal_well_ordered βord,
  have αtrans := ordinal_trans αord, have βtrans := ordinal_trans βord,
  rcases T7K αwell βwell with (RS|⟨δ, δβ, iso⟩|⟨δ, δα, iso⟩),
  { exfalso, apply αβ, rw [iso_iff_eps_img_eq αwell βwell] at RS,
    rw [eps_img_trans_well_eq_self αtrans αwell, eps_img_trans_well_eq_self βtrans βwell] at RS,
    exact RS, },
  { rw eps_order_rel_struct_fld at δβ,
    left, exact mem_of_iso_seg αord βord δβ iso, },
  { rw eps_order_rel_struct_fld at δα,
    right, exact mem_of_iso_seg βord αord δα (iso_symm iso), },
end

-- Theorem 7M part e
theorem exists_least_ord_of_nonempty {S : Set} (Sord : ∀ {x : Set}, x ∈ S → x.is_ordinal) (SE : S ≠ ∅) :
  ∃ μ : Set, μ ∈ S ∧ S.is_least S.eps_order μ :=
begin
  obtain ⟨β, βS⟩ := inhabited_of_ne_empty SE,
  by_cases βiS : β ∩ S = ∅,
  { refine ⟨_, βS, _⟩, rintro ⟨α, αS, αβ⟩, rw [eps_order, pair_mem_pair_sep] at αβ,
    apply mem_empty α, rw [←βiS, mem_inter], exact ⟨αβ.right.right, αS⟩, },
  { obtain ⟨μ, μβ, le⟩ := (ordinal_well_ordered (Sord βS)).well βiS inter_subset_left,
    rw mem_inter at μβ,
    refine ⟨_, μβ.right, _⟩, rintro ⟨α, αS, αμ⟩, rw [eps_order, pair_mem_pair_sep] at αμ,
    by_cases αβ : α ∈ β,
      apply le, use α, rw [eps_order, pair_mem_pair_sep, mem_inter],
      exact ⟨⟨αβ, αS⟩, αβ, μβ.left, αμ.right.right⟩,
    apply αβ,
    apply ord_mem_trans (Sord αS) (Sord μβ.right) (Sord βS) αμ.right.right μβ.left, },
end

lemma is_ordinal_iff {α : Set} : α.is_ordinal ↔ α.transitive_set ∧ α.well_order α.eps_order :=
⟨assume ord, ⟨ordinal_trans ord, ordinal_well_ordered ord⟩, assume ⟨trans, well⟩, eps_img_trans_well_is_ordinal trans well⟩

lemma eps_order_ordinals_lin {A : Set} (Aord : ∀ {x : Set}, x ∈ A → x.is_ordinal) : A.lin_order A.eps_order :=
begin
  refine ⟨pair_sep_sub_prod, _, _, _⟩,
  { intros x y z xy yz, rw [eps_order, pair_mem_pair_sep] at *,
    rcases xy with ⟨xA, yA, xy⟩, rcases yz with ⟨-, zA, yz⟩,
    exact ⟨xA, zA, ord_mem_trans (Aord xA) (Aord yA) (Aord zA) xy yz⟩, },
  { intros x xx, rw [eps_order, pair_mem_pair_sep] at xx,
    rcases xx with ⟨xA, -, xx⟩, exact ord_mem_irrefl (Aord xA) xx, },
  { intros x y xA yA xney, simp only [eps_order, pair_mem_pair_sep],
    cases ord_conn (Aord xA) (Aord yA) xney with xy yx,
      left, exact ⟨xA, yA, xy⟩,
    right, exact ⟨yA, xA, yx⟩, },
end

-- Corollary 7N part a
theorem trans_ords_is_ord {S : Set} (Sord : ∀ {x : Set}, x ∈ S → x.is_ordinal) (trans : S.transitive_set) : S.is_ordinal :=
begin
  rw is_ordinal_iff, refine ⟨trans, eps_order_ordinals_lin @Sord, _⟩,
  intros X XE XS,
  obtain ⟨μ, μX, le⟩ := exists_least_ord_of_nonempty (λ x xX, Sord (XS xX)) XE,
  refine ⟨_, μX, _⟩, rintro ⟨x, xX, xμ⟩, refine le ⟨_, xX, _⟩,
  rw [eps_order, pair_mem_pair_sep] at *,
  rcases xμ with ⟨-, -, xμ⟩, exact ⟨xX, μX, xμ⟩,
end

-- Corollary 7N part b
theorem zero_is_ord : is_ordinal ∅ :=
begin
  apply trans_ords_is_ord vacuous, rw transitive_set_iff, exact vacuous,
end

-- Corollary 7N part c
theorem succ_ord_of_ord {α : Set} (αord : α.is_ordinal) : α.succ.is_ordinal :=
begin
  apply trans_ords_is_ord,
    intros x xα, rw mem_succ at xα, cases xα,
      subst xα, exact αord,
    exact ord_of_mem_ord αord xα,
  rw [transitive_set, T4E (ordinal_trans αord)], exact self_sub_succ,
end

-- Corollary 7N part d
theorem Union_ords_is_ord {A : Set} (Aord : ∀ {x : Set}, x ∈ A → x.is_ordinal) : A.Union.is_ordinal :=
begin
  apply trans_ords_is_ord,
    intros x xA, rw mem_Union at xA, rcases xA with ⟨X, XA, xX⟩, exact ord_of_mem_ord (Aord XA) xX,
  rw [transitive_set_iff'], intros δ δA, rw mem_Union at δA,
  rcases δA with ⟨α, αA, δα⟩,
  have αtrans := ordinal_trans (Aord αA), rw transitive_set_iff' at αtrans,
  intros x xδ, rw mem_Union, exact ⟨_, αA, αtrans δα xδ⟩,
end

lemma ord_mem_iff_ssub {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) : α ∈ β ↔ α ⊂ β :=
begin
  split,
    intro αβ,
    have βtrans := ordinal_trans βord,
    rw transitive_set_iff' at βtrans,
    refine ⟨βtrans αβ, assume αeβ, _⟩,
    subst αeβ, exact ord_mem_irrefl αord αβ,
  rintro ⟨sub, eq⟩, cases ord_conn αord βord eq with αβ βα,
    exact αβ,
  exfalso, apply eq, rw eq_iff_subset_and_subset, refine ⟨sub, _⟩,
  have αtrans := ordinal_trans αord,
  rw transitive_set_iff' at αtrans,
  exact αtrans βα,
end

lemma ord_le_iff_sub {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) : α ≤ β ↔ α ⊆ β :=
begin
  split,
    rintro (αβ|αβ),
      rw ord_mem_iff_ssub αord βord at αβ, exact αβ.left,
    subst αβ, exact subset_self,
  intro αβ, by_cases αeβ : α = β,
    subst αeβ, right, refl,
  left, rw ord_mem_iff_ssub αord βord, exact ⟨αβ, αeβ⟩,
end

lemma Union_least_upper_bound {α β : Set} (βord : β.is_ordinal) (αβ : α ∈ β) :
  α.Union ≤ β :=
begin
  have αord := ord_of_mem_ord βord αβ,
  have hα : ∀ x : Set, x ∈ α → x.is_ordinal := λ x, assume xα, ord_of_mem_ord αord xα,
  rw ord_le_iff_sub (Union_ords_is_ord hα) βord, rw ord_mem_iff_ssub αord βord at αβ,
  intros y hy, rw mem_Union at hy, rcases hy with ⟨X, Xα, yX⟩,
  have βtrans := ordinal_trans βord, rw transitive_set_iff at βtrans,
  exact βtrans (αβ.left Xα) yX,
end

lemma succ_least_upper_bound {α β : Set} (βord : β.is_ordinal) (αβ : α ∈ β) :
  α.succ ≤ β :=
begin
  rw ord_le_iff_sub (succ_ord_of_ord (ord_of_mem_ord βord αβ)) βord,
  apply union_subset_of_subset_of_subset,
    intros x hx, rw mem_singleton at hx, subst hx, exact αβ,
  rw ←ord_le_iff_sub (ord_of_mem_ord βord αβ) βord, left, exact αβ,
end

lemma Union_le_succ {α : Set} (αord : α.is_ordinal) : α.Union ≤ α.succ :=
Union_least_upper_bound (succ_ord_of_ord αord) self_mem_succ

lemma ord_eq {α : Set} (αord : α.is_ordinal) : α = {x ∈ α | x.is_ordinal} :=
begin
  rw eq_iff_subset_and_subset, refine ⟨λ x, assume xα, _, sep_subset⟩,
  rw mem_sep, exact ⟨xα, ord_of_mem_ord αord xα⟩,
end

-- Burali-Forti Theorem
theorem not_exists_ord_set : ¬ ∃ Ω : Set, ∀ {x : Set}, x ∈ Ω ↔ x.is_ordinal :=
begin
  rintro ⟨Ω, hΩ⟩,
  have Ωord : Ω.is_ordinal, apply trans_ords_is_ord,
      intros x xΩ, rw ←hΩ, exact xΩ,
    rw transitive_set_iff, intros X XΩ x xX, rw hΩ, rw hΩ at XΩ, exact ord_of_mem_ord XΩ xX,
  apply ord_mem_irrefl Ωord, rw hΩ, exact Ωord,
end

lemma ord_le_iff_lt {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) : ¬ (α ≤ β) ↔ β ∈ α :=
begin
  split,
    intro αβ, by_cases αeβ : α = β,
      exfalso, exact αβ (or.inr αeβ),
    cases ord_conn αord βord αeβ,
      exfalso, exact αβ (or.inl h),
    exact h,
  rintros βα (αβ|αβ),
    exact ord_mem_irrefl αord (ord_mem_trans αord βord αord αβ βα),
  subst αβ, exfalso, exact ord_mem_irrefl αord βα,
end

-- exercise 18
lemma Union_max_of_exists_max {S : Set} (Sord : ∀ {x : Set}, x ∈ S → x.is_ordinal) :
  S.Union ∉ S ∧ ¬ (∃ β : Set, β ∈ S ∧  ∀ {α : Set}, α ∈ S → α ≤ β) ∧ ¬ (∃ α : Set, S.Union = α.succ)
  ∨ S.Union ∈ S ∧ ∀ {α : Set}, α ∈ S → α ≤ S.Union :=
begin
  by_cases case : S.Union ∈ S,
    refine or.inr ⟨case, λ α, assume αS, _⟩, rw ord_le_iff_sub (Sord αS) (Union_ords_is_ord @Sord),
    intros β βα, rw mem_Union, exact ⟨_, αS, βα⟩,
  have nmax : ¬∃ (β : Set), β ∈ S ∧ ∀ {α : Set}, α ∈ S → α ≤ β,
    rintro ⟨β, βS, ge⟩,
    have βe : β = S.Union, apply ext, intro γ, split,
        intro γβ, rw mem_Union, exact ⟨_, βS, γβ⟩,
      rw mem_Union, rintro ⟨α, αS, γα⟩, cases ge αS with αβ αβ,
        apply ord_mem_trans (ord_of_mem_ord (Sord αS) γα) (Sord αS) (Sord βS) γα αβ,
      subst αβ, exact γα,
    subst βe, exact case βS,
  refine or.inl ⟨case, nmax, _⟩, rintro ⟨α, αe⟩, push_neg at nmax,
  have nmax' : ¬∃ (β : Set), β ∈ S.Union ∧ ∀ {γ : Set}, γ ∈ S.Union → γ ≤ β,
    push_neg, intros β, rw mem_Union, rintro ⟨γ, γS, βγ⟩,
    rcases nmax _ γS with ⟨δ, δS, δγ⟩, rw ord_le_iff_lt (Sord δS) (Sord γS) at δγ,
    use γ, rw [mem_Union, ord_le_iff_lt (Sord γS) (ord_of_mem_ord (Sord γS) βγ)],
    exact ⟨⟨_, δS, δγ⟩, βγ⟩,
  rw αe at nmax', apply nmax', refine ⟨_, self_mem_succ, λ β, assume βα, _⟩,
  rw ←mem_succ_iff_mem, exact βα,
end

-- exercise 20
lemma finite_of_well_orderings {A R : Set} (Rwell : A.well_order R) (Rwell' : A.well_order R.inv) : A.is_finite :=
begin
  have eg : ∀ {X : Set}, X ≠ ∅ → X ⊆ A → ∃ m : Set, m ∈ X ∧ ∀ {x : Set}, x ∈ X → R.lin_le x m,
    intros X XE XA, obtain ⟨m, mX, ge⟩ := Rwell'.well XE XA,
    rw [is_least] at ge, push_neg at ge, refine ⟨_, mX, λ x, assume xX, _⟩,
    rw le_iff_not_lt Rwell.lin (XA xX) (XA mX),
    specialize ge _ xX, rw pair_mem_inv at ge, exact ge,
  let closed := λ X : Set, ∀ {y : Set}, y ∈ X → ∀ {x : Set}, x.pair y ∈ R → x ∈ X,
  have un : ∀ {X : Set}, X ≠ ∅ → X ⊆ A → closed X → ∃ m : Set, m ∈ X ∧ X = (R.seg m) ∪ {m},
    intros X XE XA cl, obtain ⟨m, mX, ge⟩ := eg XE XA, refine ⟨m, mX, _⟩,
    apply ext, intro x, rw [mem_union, mem_singleton, mem_seg, ←lin_le], split,
      exact ge, rintro (xm|xm),
        exact cl mX xm,
      subst xm, exact mX,
  have segcl : ∀ {t : Set}, t ∈ A → closed (R.seg t), intros t tA y yt x xy,
    rw mem_seg at *, exact Rwell.lin.trans xy yt,
  have segsub : ∀ {t : Set}, t ∈ A → R.seg t ⊆ A, intros t tA x xt,
    rw mem_seg at xt, replace xt := Rwell.lin.rel xt, rw pair_mem_prod at xt,
    exact xt.left,
  have Acl : closed A, intros y yA x xy, replace xy := Rwell.lin.rel xy,
    rw pair_mem_prod at xy, exact xy.left,
  let B := {x ∈ A | (R.seg x).is_finite},
  have BA : B = A, apply transfinite_ind Rwell sep_subset,
    intros x xA ind, rw mem_sep,
    by_cases se : R.seg x = ∅,
      rw [se, ←card_finite_iff_finite, card_nat zero_nat, finite_cardinal_iff_nat],
      exact ⟨xA, zero_nat⟩,
    obtain ⟨m, mx, eq⟩ := un se (segsub xA) (@segcl _ xA), rw eq,
    specialize ind mx, rw mem_sep at ind,
    exact ⟨xA, union_finite_of_finite ind.right singleton_finite⟩,
  by_cases Ae : A = ∅,
    subst Ae, rw [←card_finite_iff_finite, card_nat zero_nat, finite_cardinal_iff_nat],
    exact zero_nat,
  obtain ⟨m, mx, eq⟩ := un Ae subset_self @Acl, rw eq, rw [←BA, mem_sep] at mx,
  exact union_finite_of_finite mx.right singleton_finite,
end

-- Hartogs' Theorem
theorem exists_large_ord {A : Set} : ∃ α : Set, α.is_ordinal ∧ ¬ α ≼ A :=
begin
  let W := {x ∈ A.powerset.prod (A.prod A).powerset | ∃ B R : Set, x = B.pair R ∧ B ⊆ A ∧ B.well_order R},
  have memW : ∀ {x : Set}, x ∈ W ↔ ∃ B R : Set, x = B.pair R ∧ B ⊆ A ∧ B.well_order R,
    simp only [mem_powerset, and_imp, exists_prop, mem_sep, and_iff_right_iff_imp, mem_prod, exists_imp_distrib],
    intros X B R XBR BA Rwell, subst XBR, refine ⟨_, BA, R, _, rfl⟩,
    apply subset_trans Rwell.lin.rel, intros x xBB, rw mem_prod at xBB,
    rcases xBB with ⟨a, aB, b, bB, xab⟩, subst xab, rw pair_mem_prod, exact ⟨BA aB, BA bB⟩,
  let f : Set → Set := (λ S, if is_rel : S.snd ⊆ S.fst.prod S.fst then eps_img ⟨S.fst, S.snd, is_rel⟩ else ∅),
  obtain ⟨𝓔, mem𝓔⟩ := @replacement'' f W,
  let α : Set := {β ∈ 𝓔 | β.is_ordinal ∧ β ≼ A},
  have memα : ∀ {β : Set}, β ∈ α ↔ β.is_ordinal ∧ β ≼ A,
    simp only [and_imp, mem_sep, and_iff_right_iff_imp, dominated_iff],
    rintros β βord ⟨B, BA, f, fonto, foto⟩,  rw mem𝓔,
    let S := fun_order B β.eps_order f.inv,
    have βwell := ordinal_well_ordered βord,
    have Swell : B.well_order S, refine well_order_from_fun (into_of_onto (inv_onto_of_onto fonto foto)) _ βwell,
      rw ←T3F_b fonto.left.left, exact fonto.left,
    have iso : f.isomorphism β.eps_order_rel_struct ⟨B, S, pair_sep_sub_prod⟩,
      refine ⟨⟨fonto, foto⟩, _⟩, intros x y xβ yβ, dsimp, dsimp at xβ yβ,
      have fxB : f.fun_value x ∈ B, rw ←fonto.right.right, apply fun_value_def'' fonto.left, rw fonto.right.left, exact xβ,
      have fyB : f.fun_value y ∈ B, rw ←fonto.right.right, apply fun_value_def'' fonto.left, rw fonto.right.left, exact yβ,
      have xd : x ∈ f.dom, rw fonto.right.left, exact xβ,
      have yd : y ∈ f.dom, rw fonto.right.left, exact yβ,
      simp only [S, fun_order, pair_mem_pair_sep' fxB fyB, T3G_a fonto.left foto _ xd, T3G_a fonto.left foto _ yd],
    let P := B.pair S,
    have cond : P.snd ⊆ P.fst.prod P.fst,
      simp only [fst_congr, snd_congr], exact Swell.lin.rel,
    use P, split,
      rw memW, exact ⟨_, _, rfl, BA, Swell⟩,
    change β = if is_rel : P.snd ⊆ P.fst.prod P.fst then eps_img ⟨P.fst, P.snd, is_rel⟩ else ∅,
    simp only [dif_pos cond, fst_congr, snd_congr],
    let P' : rel_struct := ⟨B, S, Swell.lin.rel⟩,
    let β' : rel_struct := β.eps_order_rel_struct,
    have Swell' : P'.fld.well_order P'.rel := Swell,
    have βwell' : β'.fld.well_order β'.rel := βwell,
    rw ←(iso_iff_eps_img_eq βwell' Swell').mp ⟨f, iso⟩,
    symmetry, exact eps_img_trans_well_eq_self (ordinal_trans βord) βwell,
  apply classical.by_contradiction, intro all, push_neg at all,
  apply not_exists_ord_set, use α, intro β,
  simp only [memα, and_iff_left_iff_imp], exact all _,
end


end Set