import ch2

universe u

@[simp]
lemma Set.pair_mem_pair_sep {p : Set → Set → Prop} {x y a b : Set} :
a.pair b ∈ Set.pair_sep p x y ↔ a ∈ x ∧ b ∈ y ∧ p a b :=
begin
  simp only [Set.mem_pair_sep], split,
  { rintro ⟨a', ha, b', hb, he, hp⟩,
    have hpe : a = a' ∧ b = b' := Set.pair_inj he,
    simp only [hpe.left, hpe.right],
    exact ⟨ha, hb, hp⟩, },
  { rintro ⟨ha, hb, hp⟩,
    exact ⟨a, ha, b, hb, rfl, hp⟩, },
end

theorem pair_unordered {a b : Set} : ({a, b} : Set) = {b, a} :=
begin
  apply Set.ext,
  intro z,
  simp only [Set.mem_pair, or_comm],
end
-- We have x.pair y = {{x}, {x, y}}
-- And Set.pair_inj which shows injectivity of pair
-- Set.pair_sep p x y supplies us with the set of all ordered pairs from x × y that satisfies p
-- Corralary 3C is basically Set.mem_pair_sep
-- We also have Set.prod and Set.mem_prod
theorem ch3_p4 : ¬ ∃ S : Set, ∀ x y : Set, x.pair y ∈ S :=
begin
  rintro ⟨S, h⟩,
  apply univ_not_set,
  refine ⟨S.Union.Union, _⟩,
  intro x,
  specialize h x x,
  rw Set.mem_Union,
  refine ⟨{x}, _, _⟩,
  rw Set.mem_Union,
  refine ⟨x.pair x, h, _⟩,
  simp only [Set.pair, true_or, eq_self_iff_true, Set.mem_pair],
  simp only [Set.mem_singleton],
end

def Set.is_pair (x : Set) : Prop := ∃ (y z : Set), x = y.pair z
def Set.is_rel (R : Set) : Prop := ∀ x : Set, x ∈ R → x.is_pair
def Set.dom (R : Set) : Set := {x ∈ R.Union.Union | ∃ y, x.pair y ∈ R}
def Set.ran (R : Set) : Set := {x ∈ R.Union.Union | ∃ t : Set, t.pair x ∈ R}
def Set.fld (R : Set) : Set := R.dom ∪ R.ran

lemma Set.empty_is_rel : (∅ : Set).is_rel :=
begin
  intros x hx, exfalso, exact Set.mem_empty _ hx,
end

lemma Set.singleton_is_rel {x y : Set} : ({x.pair y} : Set).is_rel :=
begin
  intros z hz, rw Set.mem_singleton at hz, exact ⟨_, _, hz⟩,
end

lemma Set.inter_rel_is_rel {R : Set} (hR : R.is_rel) {S : Set} : (R ∩ S).is_rel :=
begin
  intros x hx, rw [Set.mem_inter] at hx, exact hR _ hx.left,
end

lemma Set.union_rel_is_rel {R : Set} (hR : R.is_rel) {S : Set} (hS : S.is_rel) : (R ∪ S).is_rel :=
begin
  intros x hx, rw [Set.mem_union] at hx, cases hx,
    exact hR _ hx,
  exact hS _ hx,
end

lemma Set.rel_eq {R : Set} (hR : R.is_rel) {S : Set} (hS : S.is_rel) (h : ∀ ⦃x y : Set⦄, x.pair y ∈ R ↔ x.pair y ∈ S) : R = S :=
begin
  apply Set.ext, intro z, split,
  { intro hz,
    have hxy := hR _ hz, rcases hxy with ⟨x, y, hxy⟩,
    rw hxy at hz, rw hxy, rw ←h, exact hz, },
  { intro hz,
    have hxy := hS _ hz, rcases hxy with ⟨x, y, hxy⟩,
    rw hxy at hz, rw hxy, rw h, exact hz, },
end

lemma Set.rel_eq_empty {R : Set} (hR : R.is_rel) : R = ∅ ↔ ∀ ⦃x y : Set⦄, x.pair y ∉ R :=
begin
  split,
  { intro he, simp only [he, Set.mem_empty, forall_const, not_false_iff], },
  { intro ha, apply Set.rel_eq hR Set.empty_is_rel, intros x y, split,
    { intro h, exfalso, exact ha h, },
    { intro h, exfalso, exact Set.mem_empty _ h, }, },
end

lemma Set.is_pair_of_mem_prod {p A B : Set} (h : p ∈ A.prod B) : p.is_pair :=
begin
  simp only [Set.mem_prod, exists_prop] at h, rcases h with ⟨a, ha, b, hb, he⟩,
  exact ⟨_, _, he⟩,
end

lemma Set.pair_sep_is_rel {p : Set → Set → Prop} {x y : Set} : (Set.pair_sep p x y).is_rel :=
begin
  intros z hz,
  simp only [Set.mem_pair_sep] at hz,
  rcases hz with ⟨a, ha, b, hb, he, hp⟩,
  exact ⟨a, b, he⟩,
end

lemma Set.pair_sep_sub_prod {p : Set → Set → Prop} {x y : Set} : Set.pair_sep p x y ⊆ x.prod y :=
begin
  intro p, simp only [Set.mem_pair_sep, Set.mem_prod, exists_prop], rintro ⟨a, ha, b, hb, he, hp⟩,
  exact ⟨_, ha, _, hb, he⟩,
end

lemma L3D_bulk {x y A : Set} (h : x.pair y ∈ A) : {x, y} ∈ A.Union :=
begin
  rw Set.mem_Union,
  refine ⟨_, h, _⟩,
  simp only [Set.pair, Set.mem_pair], right, refl,
end

lemma L3D_left {x y A : Set} (h : x.pair y ∈ A) : x ∈ A.Union.Union :=
begin
  rw Set.mem_Union,
  refine ⟨_, L3D_bulk h, _⟩,
  simp only [Set.mem_pair], left, refl,
end

lemma L3D_right {x y A : Set} (h : x.pair y ∈ A) : y ∈ A.Union.Union :=
begin
  rw Set.mem_Union,
  refine ⟨_, L3D_bulk h, _⟩,
  simp only [Set.mem_pair], right, refl,
end

@[simp]
lemma Set.mem_dom {R : Set} (x : Set) : x ∈ R.dom ↔ ∃ y, x.pair y ∈ R :=
begin
  simp only [Set.dom, Set.mem_sep],
  apply and_iff_right_of_left_if_right,
  rintro ⟨y, h⟩,
  exact L3D_left h,
end
@[simp]
lemma Set.mem_ran {R : Set} (x : Set) : x ∈ R.ran ↔ ∃ t : Set, t.pair x ∈ R :=
begin
  simp only [Set.ran, Set.mem_sep],
  apply and_iff_right_of_left_if_right,
  rintro ⟨t, h⟩,
  exact L3D_right h,
end

lemma Set.pair_sep_dom_sub {p : Set → Set → Prop} {x y : Set} : (Set.pair_sep p x y).dom ⊆ x :=
begin
  intros z hz, simp only [Set.mem_dom, Set.pair_mem_pair_sep] at hz, finish,
end

@[simp]
lemma Set.dom_singleton {x y : Set} : ({x.pair y} : Set).dom = {x} :=
begin
  apply Set.ext, simp only [Set.mem_singleton, Set.mem_dom], intro z, split,
  { rintro ⟨y, hy⟩, exact (Set.pair_inj hy).left, },
  { rintro hx, rw hx, exact ⟨_, rfl⟩, },
end

@[simp]
lemma Set.ran_singleton {x y : Set} : ({x.pair y} : Set).ran = {y} :=
begin
  apply Set.ext, simp only [Set.mem_singleton, Set.mem_ran], intro z, split,
  { rintro ⟨y, hy⟩, exact (Set.pair_inj hy).right, },
  { rintro hx, rw hx, exact ⟨_, rfl⟩, },
end

lemma Set.rel_sub_dom_ran {R : Set} : R.is_rel ↔ R ⊆ R.dom.prod R.ran :=
begin
  split,
    intros hR z hz, rw Set.mem_prod, specialize hR _ hz, rcases hR with ⟨x, y, hxy⟩, rw hxy at hz,
    simp only [exists_prop, Set.mem_dom, Set.mem_ran], exact ⟨_, ⟨_, hz⟩, _, ⟨_, hz⟩, hxy⟩,
  intros hR z hz, specialize hR hz, simp only [Set.mem_prod, exists_prop] at hR, rcases hR with ⟨x, hx, y, hy, he⟩,
  exact ⟨_, _, he⟩,
end

def Set.fst (p : Set) : Set := ({p} : Set).dom.Union
def Set.snd (p : Set) : Set := ({p} : Set).ran.Union

lemma Set.fst_snd_spec {p : Set} (hp : p.is_pair) : p = p.fst.pair p.snd :=
begin
  rcases hp with ⟨x, y, hp⟩, rw hp, congr,
  { rw [Set.fst, Set.dom_singleton, Set.Union_singleton], },
  { rw [Set.snd, Set.ran_singleton, Set.Union_singleton], },
end

lemma Set.fst_congr {x y : Set} : (x.pair y).fst = x :=
begin
  have h : x.pair y = (x.pair y).fst.pair (x.pair y).snd := Set.fst_snd_spec ⟨_, _, rfl⟩,
  symmetry, exact (Set.pair_inj h).left,
end

lemma Set.snd_congr {x y : Set} : (x.pair y).snd = y :=
begin
  have h : x.pair y = (x.pair y).fst.pair (x.pair y).snd := Set.fst_snd_spec ⟨_, _, rfl⟩,
  symmetry, exact (Set.pair_inj h).right,
end

lemma Set.fst_snd_mem_dom_ran {p A B : Set} (hp : p ∈ A.prod B) : p.fst ∈ A ∧ p.snd ∈ B :=
begin
  simp only [Set.mem_prod, exists_prop] at hp,
  rcases hp with ⟨a, ha, b, hb, he⟩,
  have he' : a.pair b = p.fst.pair p.snd, rw ←he, exact Set.fst_snd_spec ⟨_, _, he⟩,
  rw [←(Set.pair_inj he').left, ←(Set.pair_inj he').right], finish,
end

lemma Set.ran_subset_of_subset {H F : Set} (h : H ⊆ F) : H.ran ⊆ F.ran :=
begin
  intro z, simp only [Set.mem_ran],
  rintro ⟨x, hx⟩,
  exact ⟨x, h hx⟩,
end

theorem ch3_p6 {A : Set} : A.is_rel ↔ A ⊆ A.dom.prod A.ran :=
begin
  split; intro h,
  { intros p h₂,
    rcases h _ h₂ with ⟨x, y, h₃⟩,
    simp only [h₃, Set.pair_mem_prod, Set.mem_dom, Set.mem_ran],
    split,
      refine ⟨y, _⟩, rw ←h₃, exact h₂,
    refine ⟨x, _⟩, rw ←h₃, exact h₂, },
  { intros p h₂,
    specialize h h₂,
    simp only [Set.mem_prod] at h,
    rcases h with ⟨x, h₃, y, h₄, he⟩,
    exact ⟨x, y, he⟩, },
end

def Set.pow : Set → ℕ → Set
| S 0 := {∅}
| S 1 := S
| S (n + 1) := (S.pow n).prod S
def Set.is_n_ary (S : Set) (n : ℕ) : Prop := S ⊆ S.pow n
def Set.is_function (F : Set) : Prop := F.is_rel ∧ ∀ x : Set, x ∈ F.dom → ∃! y, x.pair y ∈ F

def Set.fun_value (F x : Set) : Set := {y ∈ F.Union.Union | x.pair y ∈ F}.Union

lemma Set.is_function_iff {F : Set} : F.is_function ↔ F.is_rel ∧ ∀ x y y' : Set, x.pair y ∈ F → x.pair y' ∈ F → y = y' :=
begin
  simp only [Set.is_function, Set.mem_dom, exists_imp_distrib, and.congr_right_iff], intro hr, split,
  { intros h x y y' hy hy', refine unique_of_exists_unique (h _ _ hy) hy hy', },
  { intros h x y hy, exact exists_unique_of_exists_of_unique ⟨_, hy⟩ (h x), },
end

@[simp]
lemma Set.mem_fun_value {F x z : Set} : z ∈ F.fun_value x ↔ ∃ y : Set, x.pair y ∈ F ∧ z ∈ y :=
begin
  simp only [Set.fun_value, Set.mem_Union], split,
  { rintro ⟨y, h₁, h₂⟩,
    simp only [Set.mem_sep] at h₁,
    exact ⟨_, h₁.right, h₂⟩, },
  { rintro ⟨y, h₁, h₂⟩,
    refine ⟨_, _, h₂⟩,
    simp only [Set.mem_sep],
    exact ⟨L3D_right h₁, h₁⟩, },
end

lemma Set.fun_lemma {F x y z : Set} (hf : F.is_function) (hy : x.pair y ∈ F) (hz : x.pair z ∈ F) : y = z :=
begin
  have hd : x ∈ F.dom, simp only [Set.mem_dom], exact ⟨_, hy⟩,
  exact unique_of_exists_unique (hf.right x hd) hy hz,
end

lemma Set.fun_value_def {F x y : Set} (hf : F.is_function) (hp : x.pair y ∈ F) : y = F.fun_value x :=
begin
  apply Set.ext, intro z, simp only [Set.mem_fun_value], split,
  { intro hm, exact ⟨_, hp, hm⟩, },
  { rintro ⟨w, hw, hm⟩,
    rw Set.fun_lemma hf hp hw,
    assumption, },
end

lemma Set.fun_value_def' {F x : Set} (hf : F.is_function) (hd : x ∈ F.dom) : x.pair (F.fun_value x) ∈ F :=
begin
  simp only [Set.mem_dom] at hd,
  rcases hd with ⟨y, hy⟩,
  rw ←Set.fun_value_def hf hy,
  exact hy,
end

lemma Set.fun_value_def'' {F x : Set} (hf : F.is_function) (hd : x ∈ F.dom) : (F.fun_value x) ∈ F.ran :=
begin
  simp only [Set.mem_ran],
  exact ⟨x, Set.fun_value_def' hf hd⟩,
end

lemma Set.fun_value_def''' {F x y : Set} (hf : F.is_function) (hd : x ∈ F.dom) (hy : y = F.fun_value x) : x.pair y ∈ F :=
begin
  rw hy, exact Set.fun_value_def' hf hd,
end

lemma Set.eq_fun_value_of_mem_ran {F y : Set} (hf : F.is_function) (hy : y ∈ F.ran) : ∃ x ∈ F.dom, y = F.fun_value x :=
begin
  rw Set.mem_ran at hy, rcases hy with ⟨x, hy⟩, refine ⟨x, _, _⟩,
  { rw Set.mem_dom, exact ⟨_, hy⟩, },
  { exact Set.fun_value_def hf hy, },
end

lemma Set.mem_ran_iff {F : Set} (hf : F.is_function) {y : Set} : y ∈ F.ran ↔ ∃ x : Set, x ∈ F.dom ∧ y = F.fun_value x :=
begin
  split,
  { intro hy,
    have h := Set.eq_fun_value_of_mem_ran hf hy,
    simp only [exists_prop] at h, assumption, },
  { rintro ⟨x, hx, he⟩, rw he, exact Set.fun_value_def'' hf hx, },
end

def Set.into_fun (F A B : Set) : Prop := F.is_function ∧ F.dom = A ∧ F.ran ⊆ B

lemma Set.fun_def_equiv {F A B : Set} : F.into_fun A B ↔ A.is_func B F :=
begin
  split,
  { rintro ⟨⟨hf, hu⟩, hd, hr⟩, refine ⟨λ p hp, _, λ x hx, _⟩,
    { simp only [Set.mem_prod], specialize hf p hp, rcases hf with ⟨x, y, he⟩,
      have hx : x ∈ A, rw [←hd, Set.mem_dom], use y, rw ←he, assumption,
      have hy : y ∈ B, apply hr, rw Set.mem_ran, use x, rw ←he, assumption,
      exact ⟨_, hx, _, hy, he⟩, },
    { rw [←hd, Set.mem_dom] at hx, apply exists_unique_of_exists_of_unique hx (λ y₁ y₂ hy₁ hy₂, _),
      refine unique_of_exists_unique (hu x _) hy₁ hy₂,
      { rw Set.mem_dom, assumption, }, }, },
  { rintro ⟨hsp, hu⟩, refine ⟨⟨λ p hp, _, λ x hx, _⟩, _, _⟩,
    { specialize hsp hp, rw Set.mem_prod at hsp, rcases hsp with ⟨x, hx, y, hp, he⟩, exact ⟨_, _, he⟩, },
    { apply hu, rw Set.mem_dom at hx, rcases hx with ⟨y, hp⟩, specialize hsp hp,
      rw Set.mem_prod at hsp, rcases hsp with ⟨a, ha, b, hb, he⟩, rw (Set.pair_inj he).left, assumption, },
    { apply Set.ext, simp only [Set.mem_dom], intro x, split,
      { rintro ⟨y, hp⟩, specialize hsp hp, rw Set.mem_prod at hsp,
        rcases hsp with ⟨a, ha, b, hb, he⟩, rw (Set.pair_inj he).left, assumption, },
      { intro hx, exact exists_of_exists_unique (hu _ hx), }, },
    { intros y hy, rw Set.mem_ran at hy, rcases hy with ⟨x, hp⟩, specialize hsp hp,
      rw Set.mem_prod at hsp, rcases hsp with ⟨a, ha, b, hb, he⟩, rw (Set.pair_inj he).right, assumption, }, },
end

lemma Set.is_function_of_into {F A B : Set} (hf : F.into_fun A B) : F.is_function := hf.left
lemma Set.dom_eq_of_into {F A B : Set} (hf : F.into_fun A B) : F.dom = A := hf.right.left
lemma Set.ran_sub_of_into {F A B : Set} (hf : F.into_fun A B) : F.ran ⊆ B := hf.right.right

def Set.onto_fun (F A B : Set) : Prop := F.is_function ∧ F.dom = A ∧ F.ran = B
def Set.one_to_one (F : Set) : Prop := ∀ y : Set, y ∈ F.ran → ∃! x : Set, x.pair y ∈ F -- also called single-rooted
def Set.inv (F : Set) : Set := Set.pair_sep (λ a b, b.pair a ∈ F) F.ran F.dom

lemma Set.one_to_one_of {F : Set} (hf : F.is_function)
(h : ∀ {m : Set}, m ∈ F.dom → ∀ {n : Set}, n ∈ F.dom → m ≠ n → F.fun_value m ≠ F.fun_value n) : F.one_to_one :=
begin
  intros y hy, rw Set.mem_ran at hy, rcases hy with ⟨x, hx⟩, refine ⟨_, hx, _⟩,
  intros x' hx', apply classical.by_contradiction, intros hne, refine @h x _ x' _ _ _,
  { rw Set.mem_dom, exact ⟨_, hx⟩, },
  { rw Set.mem_dom, exact ⟨_, hx'⟩, },
  { intro he, apply hne, symmetry, assumption, },
  { rw ←Set.fun_value_def hf hx, rw ←Set.fun_value_def hf hx', },
end

lemma Set.from_one_to_one {F : Set} (hf : F.is_function) (hoto : F.one_to_one) {x x' : Set}
(hx : x ∈ F.dom) (hx' : x' ∈ F.dom) (he : F.fun_value x = F.fun_value x') : x = x' :=
begin
  refine unique_of_exists_unique (hoto (F.fun_value x) _) _ _,
  { apply Set.fun_value_def'' hf, assumption, },
  { apply Set.fun_value_def' hf, assumption, },
  { rw he, apply Set.fun_value_def' hf, assumption, },
end

lemma Set.onto_of_into {F A B : Set} (hf : F.into_fun A B) (he : F.ran = B) : F.onto_fun A B :=
⟨Set.is_function_of_into hf, Set.dom_eq_of_into hf, he⟩

lemma Set.onto_ran_of_into {F A B : Set} (hf : F.into_fun A B) : F.onto_fun A F.ran := ⟨hf.left, hf.right.left, rfl⟩

lemma Set.into_of_onto {F A B : Set} (hf : F.onto_fun A B) : F.into_fun A B :=
begin
  rcases hf with ⟨hf, hd, hr⟩, refine ⟨hf, hd, _⟩, rw hr, exact Set.subset_self,
end

lemma Set.into_of_into_ran_sub {F A B C : Set} (h : B ⊆ C) (hf : F.into_fun A B) : F.into_fun A C :=
⟨hf.left, hf.right.left, Set.subset_trans hf.right.right h⟩

lemma Set.into_of_onto_ran_sub {F A B C : Set} (h : B ⊆ C) (hf : F.onto_fun A B) : F.into_fun A C :=
Set.into_of_into_ran_sub h (Set.into_of_onto hf)

lemma Set.union_singleton_is_fun {F : Set} (hF : F.is_function) {x y : Set} (hx : x ∉ F.dom) : (F ∪ {x.pair y}).is_function :=
begin
  rw Set.is_function_iff, split,
    exact Set.union_rel_is_rel hF.left Set.singleton_is_rel,
  intros a b b' hb hb', rw [Set.mem_union, Set.mem_singleton] at hb hb',
  rw Set.is_function_iff at hF,
  cases hb; cases hb',
        exact hF.right _ _ _ hb hb',
      exfalso, apply hx, rw Set.mem_dom, rw (Set.pair_inj hb').left at hb, exact ⟨_, hb⟩,
    exfalso, apply hx, rw Set.mem_dom, rw (Set.pair_inj hb).left at hb', exact ⟨_, hb'⟩,
  rw ←hb' at hb, exact (Set.pair_inj hb).right,
end

@[simp]
lemma Set.mem_inv {F p : Set} : p ∈ F.inv ↔ ∃ (a b : Set), p = a.pair b ∧ b.pair a ∈ F :=
begin
  simp only [Set.inv, Set.mem_pair_sep], split,
  { rintro ⟨a, ha, b, hb, he, hm⟩,
    exact ⟨_, _, he, hm⟩, },
  { rintro ⟨a, b, he, hm⟩,
    refine ⟨_, _, _, _, he, hm⟩,
    rw Set.mem_ran, exact ⟨_, hm⟩,
    rw Set.mem_dom, exact ⟨_, hm⟩, },
end

lemma Set.inv_rel {F : Set} : F.inv.is_rel := Set.pair_sep_is_rel

@[simp]
lemma Set.pair_mem_inv {F a b : Set} : a.pair b ∈ F.inv ↔ b.pair a ∈ F :=
begin
  simp only [Set.mem_inv], split,
  { rintro ⟨x, y, he, hm⟩,
    suffices hinj : a = x ∧ b = y,
      rw hinj.left, rw hinj.right, assumption,
    exact Set.pair_inj he, },
  { intro h, exact ⟨a, b, rfl, h⟩, },
end

lemma Set.inv_inv {F : Set} (hf : F.is_rel) : F.inv.inv = F :=
begin
  apply Set.rel_eq Set.inv_rel hf, simp only [Set.pair_mem_inv], finish,
end

def Set.comp (F G : Set) : Set := Set.pair_sep (λ a b, ∃ t : Set, a.pair t ∈ G ∧ t.pair b ∈ F) G.dom F.ran

lemma Set.comp_rel (F G : Set) : (F.comp G).is_rel := Set.pair_sep_is_rel

@[simp]
lemma Set.mem_comp {F G p : Set} : p ∈ F.comp G ↔ ∃ (a b c : Set), p = a.pair c ∧ a.pair b ∈ G ∧ b.pair c ∈ F :=
begin
  simp only [Set.comp, Set.mem_pair_sep], split,
  { rintro ⟨a, ha, b, hb, he, t, hm1, hm2⟩,
    exact ⟨a, t, b, he, hm1, hm2⟩, },
  { rintro ⟨a, b, c, he, hm1, hm2⟩,
    refine ⟨a, _, c, _, he, _, hm1, hm2⟩,
      rw Set.mem_dom, exact ⟨_, hm1⟩,
      rw Set.mem_ran, exact ⟨_, hm2⟩, },
end

@[simp]
lemma Set.pair_mem_comp {F G a c : Set} : a.pair c ∈ F.comp G ↔ ∃ b : Set, a.pair b ∈ G ∧ b.pair c ∈ F :=
begin
  simp only [Set.mem_comp], split,
  { rintro ⟨a', b, c', he, hg, hf⟩,
    have hinj : a = a' ∧ c = c' := Set.pair_inj he,
    rw hinj.left, rw hinj.right,
    exact ⟨_, hg, hf⟩, },
  { rintro ⟨b, hg, hf⟩,
    exact ⟨_, _, _, rfl, hg, hf⟩, },
end

def Set.restrict (F A : Set) : Set := Set.pair_sep (λ a b, a.pair b ∈ F ∧ a ∈ A) F.dom F.ran

lemma Set.restrict_is_rel {F A : Set} : (F.restrict A).is_rel := Set.pair_sep_is_rel

@[simp]
lemma Set.mem_restrict {F A p : Set} : p ∈ F.restrict A ↔ ∃ (a b : Set), p = a.pair b ∧ a.pair b ∈ F ∧ a ∈ A :=
begin
  simp only [Set.restrict, Set.mem_pair_sep], split; intro h,
    rcases h with ⟨a, H₁, b, H₂, h₁, h₂, h₃⟩, exact ⟨_, _, h₁, h₂, h₃⟩,
  rcases h with ⟨a, b, h₁, h₂, h₃⟩,
  refine ⟨a, _, b, _, _⟩,
  simp only [Set.mem_dom], exact ⟨_, h₂⟩,
  simp only [Set.mem_ran], exact ⟨_, h₂⟩,
  exact ⟨h₁, h₂, h₃⟩,
end

@[simp]
lemma Set.pair_mem_restrict {F A x y : Set} : x.pair y ∈ F.restrict A ↔ x.pair y ∈ F ∧ x ∈ A :=
begin
  simp, split,
  { rintro ⟨a, b, he, hp, hm⟩, rw he, rw (Set.pair_inj he).left, finish, },
  { rintro ⟨hp, hm⟩, exact ⟨_, _, rfl, hp, hm⟩, },
end

lemma Set.restrict_combine {F : Set} (hf : F.is_rel) {A B : Set} (hd : A ∪ B = F.dom) : F.restrict A ∪ F.restrict B = F :=
begin
  apply Set.ext, simp only [Set.mem_union, Set.mem_restrict], intro p, split,
  { rintro (⟨a, b, he, hp, hm⟩|⟨a, b, he, hp, hm⟩),
    { rw he, exact hp, },
    { rw he, exact hp, }, },
  { intro hp, have h := hf _ hp, rcases h with ⟨x, y, h⟩,
    have hx : x ∈ F.dom, rw Set.mem_dom, finish,
    rw ←hd at hx, rw Set.mem_union at hx, rcases hx with hx|hx,
    { finish, },
    { finish, }, },
end

lemma Set.restrict_singleton_eq {F : Set} (hf : F.is_function) {x : Set} (hx : x ∈ F.dom) : F.restrict {x} = {x.pair (F.fun_value x)} :=
begin
  apply Set.ext, intro p, simp only [Set.mem_singleton, Set.mem_restrict], split,
  { rintro ⟨x', y, he, hp, hm⟩, rw he, congr,
    { exact hm, },
    { rw ←hm, exact Set.fun_value_def hf hp, }, },
  { rintro he, refine ⟨_, _, he, _, rfl⟩, exact Set.fun_value_def' hf hx, },
end

lemma Set.restrict_is_function {F : Set} (hf : F.is_function) {A : Set} : (F.restrict A).is_function :=
begin
  rw Set.is_function_iff, split,
  { intro z, rw [Set.mem_restrict], rintro ⟨x, y, he, hp, hx⟩, exact ⟨_, _, he⟩, },
  { simp only [Set.pair_mem_restrict], rintros x y y' ⟨hp, hx⟩ ⟨hp', -⟩,
    rw Set.is_function_iff at hf, exact hf.right x y y' hp hp', },
end

lemma Set.restrict_fun_value {F : Set} (hf : F.is_function) {A : Set} (hA : A ⊆ F.dom) {x : Set} (hx : x ∈ A) : (F.restrict A).fun_value x = F.fun_value x :=
begin
  symmetry, apply Set.fun_value_def (Set.restrict_is_function hf), rw Set.pair_mem_restrict,
  refine ⟨Set.fun_value_def' hf (hA hx), hx⟩,
end

lemma Set.restrict_dom {F A : Set} (hA : A ⊆ F.dom) : (F.restrict A).dom = A :=
begin
  apply Set.ext, intro x, simp only [Set.mem_dom, Set.pair_mem_restrict, and_iff_right_iff_imp, exists_and_distrib_right],
  intro hxA, rw ←Set.mem_dom, exact hA hxA,
end

lemma Set.restrict_one_to_one {F : Set} (hf : F.is_function) (hoto : F.one_to_one) {A : Set} (hA : A ⊆ F.dom) : (F.restrict A).one_to_one :=
begin
  apply Set.one_to_one_of (Set.restrict_is_function hf),
  intros x hx x' hx' hne he,
  rw [Set.restrict_dom hA] at *,
  rw [Set.restrict_fun_value hf hA hx, Set.restrict_fun_value hf hA hx'] at he, apply hne,
  exact Set.from_one_to_one hf hoto (hA hx) (hA hx') he,
end

def Set.img (F A : Set) : Set := (F.restrict A).ran

@[simp]
lemma Set.mem_img {F A y : Set} : y ∈ F.img A ↔ ∃ x : Set, x ∈ A ∧ x.pair y ∈ F :=
begin
  simp only [Set.img, Set.mem_ran, Set.mem_restrict], split,
    rintro ⟨t, a, b, h₁, h₂, h₃⟩,
    have h₄ : y = b := (Set.pair_inj h₁).right,
    subst h₄,
    exact ⟨_, h₃, h₂⟩,
  rintro ⟨x, h₁, h₂⟩,
  exact ⟨x, x, y, rfl, h₂, h₁⟩,
end

lemma Set.mem_img' {F A y : Set} (h : F.is_function) (h' : A ⊆ F.dom) : y ∈ F.img A ↔ ∃ x : Set, x ∈ A ∧ y = F.fun_value x :=
begin
  simp only [Set.mem_img],
  split,
    rintro ⟨x, h₁, h₂⟩,
    refine ⟨_, h₁, Set.fun_value_def h h₂⟩,
  rintros ⟨x, h₁, h₂⟩,
  rw h₂,
  refine ⟨_, h₁, _⟩,
  apply Set.fun_value_def', exact h,
  exact h' h₁,
end

lemma Set.fun_value_mem_img {F : Set} (hf : F.is_function) {A : Set} (hd : A ⊆ F.dom) {x : Set} (h : x ∈ A) : F.fun_value x ∈ F.img A :=
begin
  rw Set.mem_img' hf hd, exact ⟨_, h, rfl⟩,
end

lemma Set.img_subset_ran {F A : Set} : F.img A ⊆ F.ran :=
begin
  intro y, simp only [Set.mem_img, Set.mem_ran, and_imp, exists_imp_distrib],
  intros x hxA hxyF, exact ⟨_, hxyF⟩,
end

lemma Set.restrict_ran {F A : Set} : (F.restrict A).ran = F.img A :=
begin
  apply Set.ext, intro y, simp only [Set.mem_ran, Set.mem_img, Set.pair_mem_restrict, and_comm],
end

lemma Set.restrict_into_fun {F D₁ D₂ R : Set} (hF : F.into_fun D₁ R) (h : D₂ ⊆ D₁) : (F.restrict D₂).into_fun D₂ R :=
begin
  refine ⟨Set.restrict_is_function hF.left, _, _⟩,
  { rw ←hF.right.left at h, exact Set.restrict_dom h, },
  { rw Set.restrict_ran, exact Set.subset_trans Set.img_subset_ran hF.right.right, },
end

lemma Set.img_ne_ran_of_ne_dom {F : Set} (hF : F.is_function) (hF' : F.one_to_one) {A : Set} (hAsub : A ⊆ F.dom) (hAne : A ≠ F.dom) : F.img A ≠ F.ran :=
begin
  intro he, apply hAne, rw Set.eq_iff_subset_and_subset, refine ⟨hAsub, _⟩, intros x hx,
  rw Set.mem_dom at hx, rcases hx with ⟨y, hx⟩,
  have hy : y ∈ F.ran, rw Set.mem_ran, exact ⟨_, hx⟩,
  rw [←he, Set.mem_img] at hy, rcases hy with ⟨x', hx', hy⟩,
  have hxx' : x = x', apply unique_of_exists_unique,
    { refine hF' y _, rw Set.mem_ran, exact ⟨_, hx⟩, },
    { exact hx, },
    { exact hy, },
  rw hxx', exact hx',
end

lemma Set.one_to_one_ext {F : Set} (hf : F.is_function) (ha : ∀ x y : Set, x ∈ F.dom → y ∈ F.dom → F.fun_value x = F.fun_value y → x = y) : F.one_to_one :=
begin
  intros y hy,
  apply exists_unique_of_exists_of_unique,
    simp only [Set.mem_ran] at hy, exact hy,
  intros x x' hx hx',
  apply ha x x',
  rw Set.mem_dom, exact ⟨_, hx⟩,
  rw Set.mem_dom, exact ⟨_, hx'⟩,
  rw ←Set.fun_value_def hf hx,
  rw ←Set.fun_value_def hf hx',
end

@[simp]
theorem T3E_a {F : Set} : F.inv.dom = F.ran :=
begin
  apply Set.ext, intro z, simp only [Set.mem_dom, Set.mem_ran, Set.pair_mem_inv],
end

@[simp]
theorem T3E_b {F : Set} : F.inv.ran = F.dom :=
begin
  apply Set.ext, intro z, simp only [Set.mem_ran, Set.mem_dom, Set.pair_mem_inv],
end

theorem T3E_c {F : Set} (h : F.is_rel) : F.inv.inv = F :=
begin
  apply Set.ext, intro z, rw Set.mem_inv, simp only [Set.pair_mem_inv], split,
  { rintro ⟨a, b, he, hm⟩, rw he, assumption, },
  { intro hm,
    specialize h _ hm,
    rcases h with ⟨a, b, he⟩,
    rw he at hm,
    exact ⟨_, _, he, hm⟩, },
end

theorem T3F_a {F : Set} : F.inv.is_function ↔ F.one_to_one :=
begin
  simp only [Set.is_function, Set.one_to_one, and_iff_right Set.inv_rel, T3E_a, Set.pair_mem_inv],
end

theorem T3F_b {F : Set} (h : F.is_rel) : F.is_function ↔ F.inv.one_to_one :=
begin
  simp only [Set.is_function, Set.one_to_one, and_iff_right h, T3E_b, Set.pair_mem_inv],
end

theorem T3G_a {F : Set} (hf : F.is_function) (ho : F.one_to_one) : ∀ x ∈ F.dom, F.inv.fun_value (F.fun_value x) = x :=
begin
  intros x hm,
  have hp : x.pair (F.fun_value x) ∈ F := Set.fun_value_def' hf hm,
  have hpinv : (F.fun_value x).pair x ∈ F.inv,
    simp only [Set.pair_mem_inv],
    exact hp,
  have hinvfun : F.inv.is_function := T3F_a.mpr ho,
  symmetry,
  exact Set.fun_value_def hinvfun hpinv,
end

theorem T3G_b {F : Set} (hf : F.is_function) (ho : F.one_to_one) : ∀ y ∈ F.ran, F.fun_value (F.inv.fun_value y) = y :=
begin
  intros y hm,
  rw ←T3E_a at hm,
  have hinvfun : F.inv.is_function := T3F_a.mpr ho,
  have hinvoto : F.inv.one_to_one := (T3F_b hf.left).mp hf,
  have h : F.inv.inv.fun_value (F.inv.fun_value y) = y := T3G_a hinvfun hinvoto y hm,
  rw T3E_c hf.left at h,
  exact h,
end

theorem T3H_a {F G : Set} (hf : F.is_function) (hg : G.is_function) : (F.comp G).is_function :=
begin
  split,
    intros p hp, rw Set.mem_comp at hp,
    rcases hp with ⟨a, b, c, he, hmg, hmf⟩,
    exact ⟨_, _, he⟩,
  intros p hp,
  rw Set.mem_dom at hp,
  rcases hp with ⟨y, hp⟩,
  refine ⟨_, hp, _⟩,
  intros w hw,
  simp only [Set.pair_mem_comp] at hp,
  simp only [Set.pair_mem_comp] at hw,
  rcases hp with ⟨u, hu⟩,
  rcases hw with ⟨v, hv⟩,
  have h : u = v := Set.fun_lemma hg hu.left hv.left,
  rw h at hu,
  apply Set.fun_lemma hf,
  exact hv.right,
  exact hu.right,
end

theorem T3H_b {F G : Set} (hf : F.is_function) (hg : G.is_function) : (F.comp G).dom = {x ∈ G.dom | G.fun_value x ∈ F.dom} :=
begin
  apply Set.ext, intro x, simp only [Set.mem_sep, Set.mem_dom, Set.pair_mem_comp],
  split,
  { rintro ⟨y, t, hx, ht⟩,
    refine ⟨⟨t, hx⟩, y, _⟩,
    rw ←Set.fun_value_def hg hx,
    exact ht, },
  { rintro ⟨⟨t, ht⟩, y, hy⟩,
    refine ⟨y, _, ht, _⟩,
    rw Set.fun_value_def hg ht,
    exact hy, },
end

theorem T3H_c {F G x : Set} (hf : F.is_function) (hg : G.is_function) (hd : x ∈ (F.comp G).dom) : (F.comp G).fun_value x = F.fun_value (G.fun_value x) :=
begin
  simp only [T3H_b hf hg, Set.mem_sep, Set.mem_dom] at hd,
  rcases hd with ⟨⟨t, ht⟩, y, hy⟩,
  symmetry,
  apply Set.fun_value_def (T3H_a hf hg),
  simp only [Set.pair_mem_comp],
  refine ⟨_, ht, _⟩,
  rw ←Set.fun_value_def hf hy,
  rw Set.fun_value_def hg ht,
  exact hy,
end

theorem T3I {F G : Set} : (F.comp G).inv = G.inv.comp F.inv :=
begin
  apply Set.ext, intro z, simp only [Set.mem_inv, Set.pair_mem_comp, Set.mem_comp, Set.pair_mem_inv],
  split,
  { rintro ⟨a, b, he, b', t, a', hpe, hg, hf⟩,
    have hinj : b = b' ∧ a = a' := Set.pair_inj hpe,
    refine ⟨a, t, b, he, _, _⟩,
      rw hinj.right,
      assumption,
    rw hinj.left,
    assumption, },
  { rintro ⟨a, t, b, he, hf, hg⟩,
    exact ⟨a, b, he, b, t, a, rfl, hg, hf⟩, },
end

lemma Set.dom_comp_sub {F G : Set} : (F.comp G).dom ⊆ G.dom :=
begin
  intros x hx, simp only [Set.mem_dom, Set.pair_mem_comp] at *, finish,
end

lemma Set.dom_comp {F G : Set} (h : G.ran ⊆ F.dom) : (F.comp G).dom = G.dom :=
begin
  rw Set.eq_iff_subset_and_subset, split,
  { exact Set.dom_comp_sub, },
  { intros x hx, simp only [Set.mem_dom, Set.pair_mem_comp] at *,
    rcases hx with ⟨y, hy⟩,
    have hd : y ∈ F.dom, apply h, rw Set.mem_ran, finish,
    rw Set.mem_dom at hd, finish, },
end

lemma Set.ran_comp_sub {F G : Set} : (F.comp G).ran ⊆ F.ran :=
begin
  rw [←T3E_a, T3I, ←T3E_a], exact Set.dom_comp_sub,
end

lemma Set.ran_comp {F G : Set} (h : F.dom ⊆ G.ran) : (F.comp G).ran = F.ran :=
begin
  rw [←T3E_a, ←T3E_b] at h, rw [←T3E_a, T3I, ←T3E_a], exact Set.dom_comp h,
end

lemma Set.comp_into_fun {A B C f : Set} (hf : f.into_fun A B) {g : Set} (hg : g.into_fun B C) : (g.comp f).into_fun A C :=
begin
  refine ⟨T3H_a hg.left hf.left, _, _⟩,
  { have h : f.ran ⊆ g.dom, rw hg.right.left, exact hf.right.right,
    rw ←hf.right.left, exact Set.dom_comp h, },
  { apply Set.subset_trans, exact Set.ran_comp_sub, exact hg.right.right, },
end

lemma Set.inv_into_fun {f A B : Set} (hfun : f.onto_fun A B) (foto : f.one_to_one) : f.inv.into_fun B A :=
begin
  refine ⟨T3F_a.mpr foto, _, _⟩,
  { rw T3E_a, exact hfun.right.right, },
  { rw [T3E_b, hfun.right.left], exact Set.subset_self, },
end

lemma Set.fun_ext {F G : Set} (hf : F.is_function) (hg : G.is_function) (hd : F.dom = G.dom) (ha : ∀ x ∈ F.dom, F.fun_value x = G.fun_value x) : F = G :=
begin
  have h : ∀ F G : Set, F.is_function → G.is_function → F.dom = G.dom → (∀ x ∈ F.dom, F.fun_value x = G.fun_value x) → ∀ z : Set, z ∈ F → z ∈ G,
    intros F G hf hg hd ha z hm,
    have hp : z.is_pair := hf.left _ hm,
    rcases hp with ⟨x, y, hp⟩, subst hp,
    have hxd : x ∈ F.dom, simp only [Set.mem_dom], exact ⟨_, hm⟩,
    specialize ha _ hxd,
    rw ←Set.fun_value_def hf hm at ha,
    rw ha,
    rw hd at hxd,
    exact Set.fun_value_def' hg hxd,
  apply Set.ext, intro z, split,
  { exact h F G hf hg hd ha z, },
  { refine h G F hg hf hd.symm _ z,
    rw ←hd, intros x hx, exact (ha x hx).symm, },
end

lemma Set.union_of_rel_is_rel {A B : Set} (hA : A.is_rel) (hB : B.is_rel) : (A ∪ B).is_rel :=
begin
  intros x hx,
  simp only [Set.mem_union] at hx,
  cases hx,
    exact hA _ hx,
  exact hB _ hx,
end

lemma Set.prod_is_rel {A B : Set} : (A.prod B).is_rel :=
begin
  intros x hx,
  simp only [Set.mem_prod] at hx,
  rcases hx with ⟨a, ha, b, hb, he⟩,
  exact ⟨_, _, he⟩,
end

def Set.id (A : Set) : Set := Set.pair_sep (λ a b, a = b) A A

lemma Set.id_is_function {A : Set} : A.id.is_function :=
begin
  refine ⟨Set.pair_sep_is_rel, _⟩,
  simp only [Set.mem_dom, Set.pair_mem_pair_sep, Set.id],
  rintros x ⟨y, hx⟩,
  refine ⟨y, hx, _⟩,
  intros y' hy,
  rw ←hx.right.right,
  rw ←hy.right.right,
end

lemma Set.id_onto {A : Set} : A.id.onto_fun A A :=
begin
  simp only [Set.onto_fun],
  refine ⟨Set.id_is_function, _, _⟩,
    apply Set.ext, simp only [Set.mem_dom, Set.id, Set.pair_mem_pair_sep],
    intro z, split,
    { rintro ⟨y, h, _⟩, exact h, },
    { intro h, exact ⟨_, h, h, rfl⟩, },
  apply Set.ext, simp only [Set.mem_ran, Set.id, Set.pair_mem_pair_sep],
  intro z, split,
  { rintro ⟨x, _, h, _⟩, exact h, },
  { intro h, exact ⟨_, h, h, rfl⟩, },
end

lemma Set.id_into {A : Set} : A.id.into_fun A A := Set.into_of_onto Set.id_onto

lemma Set.id_value {A x : Set} (hx : x ∈ A) : A.id.fun_value x = x :=
begin
  have h : x.pair x ∈ A.id,
    simp only [Set.id, Set.pair_mem_pair_sep],
    exact ⟨hx, hx, rfl⟩,
  rw ←Set.fun_value_def Set.id_is_function h,
end

lemma Set.id_oto {A : Set} : A.id.one_to_one :=
begin
  apply Set.one_to_one_of Set.id_is_function, intros m hm n hn hne he, apply hne,
  rw Set.id_onto.right.left at hm, rw Set.id_onto.right.left at hn,
  rw ←Set.id_value hm, rw he, rw Set.id_value hn,
end

lemma Set.id_inv {A : Set} : A.id.inv = A.id :=
begin
  apply Set.rel_eq Set.inv_rel Set.id_is_function.left,
  simp only [Set.pair_mem_inv, Set.id, Set.pair_mem_pair_sep],finish,
end

lemma Set.comp_id {f : Set} (hf : f.is_function) : f.comp f.dom.id = f :=
begin
  have hd : (f.comp f.dom.id).dom = f.dom,
    have h : f.dom.id.ran ⊆ f.dom, rw Set.id_onto.right.right, exact Set.subset_self,
    rw [Set.dom_comp h, Set.id_onto.right.left],
  apply Set.fun_ext (T3H_a hf Set.id_is_function) hf hd,
  intros x hx, rw T3H_c hf Set.id_onto.left hx, rw hd at hx, rw Set.id_value hx,
end

lemma Set.id_comp {A f : Set} (hA : f.ran ⊆ A) (hf : f.is_function) : A.id.comp f = f :=
begin
  have hd : (A.id.comp f).dom = f.dom,
    have h : f.ran ⊆ A.id.dom, rw Set.id_onto.right.left, exact hA,
    rw Set.dom_comp h,
  apply Set.fun_ext (T3H_a Set.id_is_function hf) hf hd,
  intros x hx, rw T3H_c Set.id_onto.left hf hx,
  have h : f.fun_value x ∈ A, apply hA, apply Set.fun_value_def'' hf, rw hd at hx, exact hx,
  rw Set.id_value h,
end

lemma Set.eq_id {f : Set} (hf : f.is_function) (hf' : f.one_to_one) : f.inv.comp f = f.dom.id :=
begin
  apply Set.ext, intro z, simp only [Set.mem_comp, Set.id, Set.mem_pair_sep, exists_prop, Set.mem_dom, Set.pair_mem_inv], split,
  { rintro ⟨x, y, x', he, hxy, hxy'⟩, refine ⟨_, ⟨_, hxy⟩, _, ⟨_, hxy'⟩, he, _⟩,
    refine unique_of_exists_unique _ hxy hxy', apply hf', rw Set.mem_ran, exact ⟨_, hxy⟩, },
  { rintro ⟨x, ⟨y, hxy⟩, x', ⟨y', hxy'⟩, he, hxx'⟩, rw hxx' at hxy he,
    have hyy' : y = y', refine unique_of_exists_unique _ hxy hxy', apply hf.right,
      rw Set.mem_dom, exact ⟨_, hxy⟩,
    rw hyy' at hxy, exact ⟨_, _, _, he, hxy, hxy⟩, },
end

lemma Set.eq_inv_id {f : Set} (hf : f.is_function) (hf' : f.one_to_one) : f.comp f.inv = f.ran.id :=
begin
  have h : f.inv.inv.comp f.inv = f.inv.dom.id, apply Set.eq_id,
    { rw T3F_a, exact hf' },
    { rw ←T3F_b hf.left, exact hf, },
  rw [Set.inv_inv hf.left, T3E_a] at h, exact h,
end

lemma Set.union_fun {F G : Set} (hf : F.is_function) (hg : G.is_function) (hdisj : F.dom ∩ G.dom = ∅) : (F ∪ G).onto_fun (F.dom ∪ G.dom) (F.ran ∪ G.ran) :=
begin
  have hd : (F ∪ G).dom = F.dom ∪ G.dom,
    apply Set.ext, simp only [Set.mem_dom, Set.mem_union],
    intro z,
    exact exists_or_distrib,
  split,
  { refine ⟨Set.union_of_rel_is_rel hf.left hg.left, _⟩,
    simp only [hd, Set.mem_union, Set.mem_dom],
    rintros x (⟨y, hmf⟩ | ⟨y, hmg⟩),
    { refine ⟨y, or.inl hmf, _⟩,
      rintros z (hz | hz),
      exact Set.fun_lemma hf hz hmf,
      exfalso,
      apply Set.mem_empty x,
      simp only [←hdisj, Set.mem_inter, Set.mem_dom],
      exact ⟨⟨_, hmf⟩, _, hz⟩, },
    { refine ⟨y, or.inr hmg, _⟩,
      rintros z (hz | hz),
      exfalso,
      apply Set.mem_empty x,
      simp only [←hdisj, Set.mem_inter, Set.mem_dom],
      exact ⟨⟨_, hz⟩, _, hmg⟩,
      exact Set.fun_lemma hg hz hmg, }, },
  refine ⟨hd, _⟩,
  apply Set.ext, simp only [Set.mem_ran, Set.mem_union],
  intro z,
  exact exists_or_distrib,
end

lemma Set.union_fun_into_fun {F G D₁ D₂ R : Set} (hF : F.into_fun D₁ R) (hG : G.into_fun D₂ R) (hdisj : D₁ ∩ D₂ = ∅) : (F ∪ G).into_fun (D₁ ∪ D₂) R :=
begin
  have onto : (F ∪ G).onto_fun (F.dom ∪ G.dom) (F.ran ∪ G.ran), apply Set.union_fun hF.left hG.left, rw [hF.right.left, hG.right.left], exact hdisj,
  rw [←hF.right.left, ←hG.right.left], refine ⟨onto.left, onto.right.left, _⟩,
  rw onto.right.right, exact Set.union_subset_of_subset_of_subset hF.right.right hG.right.right,
end

lemma Set.ran_union {F G : Set} : (F ∪ G).ran = F.ran ∪ G.ran :=
begin
  apply Set.ext, intro x, simp only [Set.mem_ran, Set.mem_union], exact exists_or_distrib,
end

lemma Set.ran_single_pair {x y : Set} : ({x.pair y} : Set).ran = {y} :=
begin
  apply Set.ext, intro y, simp only [Set.mem_ran, Set.mem_singleton], split,
  { rintro ⟨x, hx⟩, exact (Set.pair_inj hx).right, },
  { intro hy, rw hy, exact ⟨_, rfl⟩, },
end

lemma Set.union_one_to_one {f : Set} (hf : f.one_to_one) {g : Set} (hg : g.one_to_one) (hfg : f.ran ∩ g.ran = ∅) : (f ∪ g).one_to_one :=
begin
  intros y hy, simp only [Set.mem_ran, Set.mem_union] at hy, simp only [Set.mem_union], rcases hy with ⟨x, hx|hx⟩,
  { refine ⟨_, or.inl hx, _⟩,
    have hyfr : y ∈ f.ran, rw Set.mem_ran, exact ⟨_, hx⟩,
    rintros x' (hx'|hx'),
    { apply unique_of_exists_unique (hf _ hyfr) hx' hx, },
    { have hygr : y ∈ g.ran, rw Set.mem_ran, exact ⟨_, hx'⟩,
      exfalso, apply Set.mem_empty y, rw [←hfg, Set.mem_inter], exact ⟨hyfr, hygr⟩, }, },
  { refine ⟨_, or.inr hx, _⟩,
    have hygr : y ∈ g.ran, rw Set.mem_ran, exact ⟨_, hx⟩,
    rintros x' (hx'|hx'),
    { have hyfr : y ∈ f.ran, rw Set.mem_ran, exact ⟨_, hx'⟩,
      exfalso, apply Set.mem_empty y, rw [←hfg, Set.mem_inter], exact ⟨hyfr, hygr⟩, },
    { apply unique_of_exists_unique (hg _ hygr) hx' hx, }, },
end

lemma Set.restrict_union_eq {F G : Set} (hF : F.is_rel) (hdisj : F.dom ∩ G.dom = ∅) : (F ∪ G).restrict F.dom = F :=
begin
  apply Set.rel_eq Set.restrict_is_rel hF, simp only [Set.pair_mem_restrict, Set.mem_union], intros x y, split,
  { rintro ⟨(hxy|hxy), hd⟩,
      exact hxy,
    exfalso, apply Set.mem_empty x, rw ←hdisj, rw Set.mem_inter, refine ⟨hd, _⟩, rw Set.mem_dom, exact ⟨_, hxy⟩, },
  { intro hxy, rw Set.mem_dom, refine ⟨or.inl hxy, _, hxy⟩, },
end

lemma Set.single_pair_oto {x y : Set} : ({x.pair y} : Set).one_to_one :=
begin
  intros z hz, rw [Set.ran_single_pair, Set.mem_singleton] at hz, simp only [Set.mem_singleton, hz],
  refine ⟨_, rfl, _⟩, intros x' hx', exact (Set.pair_inj hx').left,
end

lemma Set.single_pair_into {x y R : Set} (hy : y ∈ R) : ({x.pair y} : Set).into_fun {x} R :=
begin
  rw Set.fun_def_equiv, split,
    intros p hp, rw Set.mem_singleton at hp, rw [hp, Set.pair_mem_prod, Set.mem_singleton], exact ⟨rfl, hy⟩,
  simp only [Set.mem_singleton], intros z he, rw he, exact ⟨_, rfl, λ y' he', (Set.pair_inj he').right⟩,
end

lemma Set.single_pair_fun_value {x y : Set} : ({x.pair y} : Set).fun_value x = y :=
begin
  symmetry, apply Set.fun_value_def (@Set.single_pair_into _ _ {y} _).left,
    rw Set.mem_singleton,
  rw Set.mem_singleton,
end

lemma Set.single_pair_onto {x y : Set} : Set.onto_fun {x.pair y} {x} {y} :=
begin
  apply Set.onto_of_into,
    apply Set.single_pair_into, rw Set.mem_singleton,
  exact Set.ran_single_pair,
end

lemma Set.prod_singleton_fun {A x : Set} : (A.prod {x}).is_function :=
begin
  refine ⟨Set.prod_is_rel, _⟩,
  simp only [Set.mem_dom, Set.mem_singleton, Set.pair_mem_prod],
  rintros z ⟨y, hy⟩,
  refine ⟨y, hy, _⟩,
  intros y' hy',
  rw hy'.right, symmetry, exact hy.right,
end

lemma Set.dom_prod_nonempty {A B : Set} (hb : ∃ x : Set, x ∈ B) : (A.prod B).dom = A :=
begin
  apply Set.ext, intro z,
  simp only [hb, Set.mem_dom, and_true, Set.pair_mem_prod, exists_and_distrib_left],
end

lemma Set.ran_prod_nonempty {A B : Set} : (A.prod B).ran ⊆ B :=
begin
  intros z hz,
  simp only [Set.mem_ran, Set.pair_mem_prod] at hz,
  rcases hz with ⟨t, hA, hB⟩, exact hB,
end

local attribute [instance] classical.prop_decidable

lemma T3J_a {F A B : Set} (hf : F.into_fun A B) (hne : ∃ x, x ∈ A) : (∃ G : Set, G.into_fun B A ∧ G.comp F = A.id) ↔ F.one_to_one :=
begin
  simp only [Set.into_fun] at *,
  split,
  { rintro ⟨G, hif, hcid⟩,
    apply Set.one_to_one_ext hf.left,
    intros x y hxd hyd he,
    simp only [hf.right.left] at hxd hyd,
    rw ←Set.id_value hxd, rw ←Set.id_value hyd, rw ←hcid,
    rw T3H_c hif.left hf.left _,
    rw T3H_c hif.left hf.left _,
    rw he,
    simp only [hcid, (Set.id_onto).right.left, hyd],
    simp only [hcid, (Set.id_onto).right.left, hxd], },
  { rcases hne with ⟨x, hxm⟩,
    intro hoto,
    let F' := F.inv,
    let E := (B \ F.ran).prod {x},
    let G := F' ∪ E,
    have honto : G.onto_fun (F'.dom ∪ E.dom) (F'.ran ∪ E.ran),
      refine Set.union_fun _ _ _,
      { simp only [T3F_a, hoto], },
      { exact Set.prod_singleton_fun, },
      { simp only [eq_empty],
        intros z hz,
        simp only [Set.mem_inter, Set.mem_dom, Set.pair_mem_prod, Set.mem_diff, Set.pair_mem_inv, Set.mem_ran] at hz,
        rcases hz with ⟨⟨y, hy⟩, y', ⟨_, him⟩, _⟩,
        exact him ⟨_, hy⟩, },
    refine ⟨_, ⟨honto.left, _, _⟩, _⟩,
    { rw honto.right.left,
      simp only [T3E_a, Set.dom_prod_nonempty ⟨x, Set.mem_singleton.mpr rfl⟩],
      apply Set.ext, intro z,
      have hz : z ∈ F.ran → z ∈ B,
        apply Set.subset_def.mp, exact hf.right.right,
      simp only [Set.mem_union, Set.mem_diff, or_and_distrib_left, classical.em, and_true, or_iff_right_of_imp hz], },
    { rw honto.right.right,
      intros z hz,
      simp only [Set.mem_union, T3E_b] at hz,
      cases hz,
      { rw ←hf.right.left, assumption, },
      { have hz' : z ∈ {x},
          apply Set.ran_prod_nonempty,
          exact hz,
        simp only [Set.mem_singleton] at hz', rw hz', assumption, }, },
    have hcdom : (G.comp F).dom = A,
      apply Set.ext, intro z, simp only [T3H_b honto.left hf.left, Set.mem_sep, hf.right.left, Set.mem_dom],
      split,
      { rintro ⟨hmz, _⟩, assumption, },
      { intro hmz, refine ⟨hmz, _⟩,
        existsi z,
        simp only [Set.mem_union, Set.pair_mem_inv],
        apply or.inl, apply Set.fun_value_def' hf.left, rw hf.right.left, assumption, },
      apply Set.fun_ext,
      exact T3H_a honto.left hf.left,
      exact Set.id_is_function,
    simp only [Set.id_onto.right.left, hcdom],
    intros z hz, rw hcdom at hz,
    have hz' : z ∈ (G.comp F).dom, rw hcdom, assumption,
    simp only [Set.id_value hz, T3H_c honto.left hf.left hz'],
    symmetry,
    apply Set.fun_value_def honto.left,
    simp only [Set.mem_union, Set.pair_mem_inv],
    apply or.inl,
    apply Set.fun_value_def' hf.left, rw hf.right.left, assumption, },
end

-- For choice, we have Set.choice which satisfies the property that if x is a set and it does not contain the empty set,
-- then x.choice is a function with domain x and range x.Union and where the value of x.choice at a is a member of a for a in x.

lemma Set.choice_is_fun (x : Set) (h : ∅ ∉ x) : x.choice.into_fun x x.Union :=
begin
  have choice := Set.choice_is_func x h,
  have hd : x.choice.dom = x,
    apply Set.ext,
    intro z,
    simp only [Set.mem_dom],
    split,
    { rintro ⟨y, hy⟩,
      exact (Set.pair_mem_prod.mp (choice.1 hy)).1, },
    { intro mz,
      apply exists_of_exists_unique,
      exact choice.2 _ mz, },
  refine ⟨⟨_, _⟩, _, _⟩,
  { intros z hz,
    have hp := choice.left hz,
    simp only [Set.mem_prod] at hp,
    rcases hp with ⟨a, H, b, H, he⟩,
    exact ⟨a, b, he⟩, },
  { intros z hz, rw hd at hz,
    exact choice.2 _ hz, },
  { exact hd },
  { intros z hz, simp only [Set.mem_ran] at hz,
    cases hz with t hz,
    have hp : t.pair z ∈ x.prod x.Union,
      exact choice.1 hz,
    exact (Set.pair_mem_prod.mp hp).2, },
end

lemma Set.choice_mem' (x : Set.{u}) (hx : ∅ ∉ x) (y : Set) (hy : y ∈ x) : x.choice.fun_value y ∈ y :=
begin
  have hf := (Set.choice_is_fun x hx),
  have h : (x.choice : Class.{u}).fval (y : Class.{u}) = (x.choice.fun_value y : Class.{u}),
    apply Class.iota_val, intro v, split,
    { rintro ⟨a, ha, hp⟩,
      simp only [Class.mem_hom_right] at hp,
      apply Set.fun_value_def, exact hf.left, rw ←(Class.of_Set.inj ha), assumption, },
    { intro hv, refine ⟨y, rfl, _⟩,
      simp only [Class.mem_hom_right], rw hv, apply Set.fun_value_def', exact hf.left,
      rw (Set.choice_is_fun x hx).right.left, assumption, },
  suffices h₂ : (x.choice.fun_value y : Class.{u}) ∈ (y : Class.{u}),
    simp only [Class.mem_hom_left, Class.mem_hom_right] at h₂, assumption,
  rw ←h, exact Set.choice_mem x hx y hy,
end

namespace Set
lemma pair_sep_eq_is_fun {A B : Set} {f : Set → Set} : (pair_sep (λ a b, b = f a) A B).is_function :=
begin
  rw is_function_iff, split,
  { exact pair_sep_is_rel, },
  { simp only [pair_mem_pair_sep, and_imp],
    intros, finish, },
end

lemma pair_sep_eq_dom_eq {A B : Set} {f : Set → Set} (h : ∀ a ∈ A, f a ∈ B) : (pair_sep (λ a b, b = f a) A B).dom = A :=
begin
  apply ext, intro a,
  simp only [mem_dom, pair_mem_pair_sep, exists_eq_right, exists_and_distrib_left, and_iff_left_iff_imp],
  intro ha, finish,
end

lemma pair_sep_eq_ran_eq {A B : Set} {f : Set → Set} (h : ∀ b ∈ B, ∃ a, a ∈ A ∧ b = f a)
: (pair_sep (λ a b, b = f a) A B).ran = B :=
begin
  apply ext, intro b, simp only [mem_ran, pair_mem_pair_sep], split,
  { rintro ⟨t, _, hb, _⟩, assumption, },
  { intro hb, specialize h _ hb, finish, },
end

lemma pair_sep_eq_ran_sub {A B : Set} {p : Set → Set → Prop} : (pair_sep p A B).ran ⊆ B :=
begin
  intros b hb, simp only [mem_ran, pair_mem_pair_sep] at hb, finish,
end

lemma pair_sep_eq_oto {A B : Set} {f : Set → Set} (hf : ∀ ⦃a₁ : Set⦄, a₁ ∈ A → ∀ ⦃a₂ : Set⦄, a₂ ∈ A → f a₁ = f a₂ → a₁ = a₂) : (pair_sep (λ a b, b = f a) A B).one_to_one :=
begin
  intros b hb, simp only [mem_ran, pair_mem_pair_sep] at hb, rcases hb with ⟨a, ha, hb, he⟩,
  simp only [pair_mem_pair_sep], refine ⟨_, ⟨ha, hb, he⟩, λ a' ha', _⟩, rcases ha' with ⟨ha', -, he'⟩,
  rw he' at he, exact hf ha' ha he,
end

def pair_sep_eq (A B : Set) (f : Set → Set) : Set := pair_sep (λ a b, b = f a) A B

@[simp]
lemma pair_mem_pair_sep_eq {A B : Set} {f : Set → Set} {a b : Set} : a.pair b ∈ pair_sep_eq A B f ↔ a ∈ A ∧ b ∈ B ∧ b = f a :=
by simp only [pair_sep_eq, pair_mem_pair_sep]

lemma pair_sep_eq_fun_value {A B : Set} {f : Set → Set} {a : Set} (ha : a ∈ (pair_sep_eq A B f).dom) : (pair_sep_eq A B f).fun_value a = f a :=
begin
  symmetry, apply fun_value_def pair_sep_eq_is_fun, rw [pair_mem_pair_sep],
  simp only [mem_dom, pair_mem_pair_sep_eq] at ha, rcases ha with ⟨b, ha, hb, he⟩, rw he at hb,
  exact ⟨ha, hb, rfl⟩,
end

lemma pair_sep_eq_into {A B : Set} {f : Set → Set} (h : ∀ a ∈ A, f a ∈ B) : (pair_sep_eq A B f).into_fun A B :=
⟨pair_sep_eq_is_fun, pair_sep_eq_dom_eq h, pair_sep_eq_ran_sub⟩
end Set

-- These are all stated and proved equivalent in chapter 6, but some are stated earlier.

def Axiom_of_choice_I : Prop := ∀ {R : Set}, R.is_rel → ∃ F : Set, F.is_function ∧ F ⊆ R ∧ F.dom = R.dom
def Axiom_of_choice_II : Prop := ∀ {I H : Set}, (H.is_function ∧ H.dom = I ∧ (∀ i : Set, i ∈ I → H.fun_value i ≠ ∅))
→ ∃ f : Set, f.is_function ∧ f.dom = I ∧ ∀ i : Set, i ∈ I → f.fun_value i ∈ H.fun_value i
def Axiom_of_choice_III : Prop := ∀ {A : Set}, ∃ F : Set, F.is_function ∧ F.dom = {x ∈ A.powerset | x ≠ ∅}
∧ ∀ B : Set, B ∈ F.dom → F.fun_value B ∈ B
def Axiom_of_choice_IV : Prop := ∀ {𝓐 : Set}, (∀ a ∈ 𝓐, a ≠ ∅ ∧ ∀ b ∈ 𝓐, b ≠ a → a ∩ b = ∅)
→ ∃ C : Set, ∀ B ∈ 𝓐, ∃ x : Set, C ∩ B = {x}

theorem ax_ch_3 : Axiom_of_choice_III :=
begin
  intro A,
  let A' := {x ∈ A.powerset | x ≠ ∅},
  have hne : ∅ ∉ A', intro h, simp at h, assumption,
  have hf := Set.choice_is_fun _ hne,
  refine ⟨A'.choice, hf.left, _, (λ B hB, _)⟩,
  { apply Set.ext, intro z, simp only [hf.right.left, Set.mem_sep, Set.mem_dom], },
  { apply Set.choice_mem' _ hne,
    rw hf.right.left at hB, assumption, },
end

-- set_option pp.universes true

lemma choice_equiv : list.tfae [Axiom_of_choice_I.{u}, Axiom_of_choice_II.{u}, Axiom_of_choice_III.{u}, Axiom_of_choice_IV.{u}] :=
begin
  tfae_have : 1 → 2,
  { dsimp only [Axiom_of_choice_I, Axiom_of_choice_II], rintros ax1 I H ⟨Hfun, Hdom, Hne⟩,
    let R : Set := Set.pair_sep (λ i y, y ∈ H.fun_value i) I H.ran.Union,
    specialize @ax1 R Set.pair_sep_is_rel, rcases ax1 with ⟨F, Ffun, FR, Fdom⟩,
    have Rdom : R.dom = I, rw Set.eq_iff_subset_and_subset, split,
        exact Set.pair_sep_dom_sub,
      intros i hi, simp only [Set.mem_dom, Set.pair_mem_pair_sep],
      specialize Hne _ hi, replace Hne := inhabited_of_ne_empty Hne,
      rcases Hne with ⟨y, hy⟩, simp only [Set.mem_Union, exists_prop],
      refine ⟨_, hi, ⟨_, _, hy⟩, hy⟩, apply Set.fun_value_def'' Hfun, rw Hdom, exact hi,
    rw Rdom at Fdom, refine ⟨_, Ffun, Fdom, _⟩, intros i hi,
    have hiy : i.pair (F.fun_value i) ∈ R, apply FR, apply Set.fun_value_def' Ffun, rw Fdom, exact hi,
    simp only [Set.pair_mem_pair_sep] at hiy, exact hiy.right.right, },
  tfae_have : 2 → 4,
  { dsimp only [Axiom_of_choice_II, Axiom_of_choice_IV], rintros ax2 A hA,
    let H := A.id,
    have Hh : ∀ i : Set, i ∈ H.dom → H.fun_value i ≠ ∅, rw Set.id_into.right.left,
      intros i hi, rw Set.id_value hi, specialize hA _ hi, exact hA.left,
    specialize ax2 ⟨Set.id_is_function, rfl, Hh⟩, rcases ax2 with ⟨f, ffun, fdom, hf⟩, use f.ran,
    intros B hBA, use f.fun_value B, apply Set.ext, simp only [Set.mem_singleton, Set.mem_inter, Set.mem_ran],
    rw Set.id_into.right.left at hf, intro C, split,
      rintros ⟨⟨X, hXC⟩, hCB⟩, have hXA : X ∈ f.dom, rw Set.mem_dom, exact ⟨_, hXC⟩, rw [fdom, Set.id_into.right.left] at hXA,
      have hCfX : C = f.fun_value X := Set.fun_value_def ffun hXC, rw hCfX,
      suffices hXB : X = B, rw hXB,
      apply classical.by_contradiction, intro hXB, apply @Set.mem_empty (f.fun_value X),
      rw [←(hA _ hBA).right _ hXA hXB, Set.mem_inter], split,
        rw ←hCfX, exact hCB,
      specialize hf X hXA, rw Set.id_value hXA at hf, exact hf,
    intro he, split,
      use B, refine Set.fun_value_def''' ffun _ he, rw [fdom, Set.id_into.right.left], exact hBA,
    specialize hf _ hBA, rw [Set.id_value hBA] at hf, rw he, exact hf, },
  tfae_have : 4 → 3,
  { dsimp only [Axiom_of_choice_IV, Axiom_of_choice_III], rintro ax4 A,
    let 𝓐 := {x ∈ (A.powerset.Union ∪ A.powerset).powerset.powerset.powerset | ∃ B, B ⊆ A ∧ B ≠ ∅ ∧ x = Set.prod {B} B},
    have h𝓐 : ∀ x, x ∈ 𝓐 ↔ ∃ B, B ⊆ A ∧ B ≠ ∅ ∧ x = Set.prod {B} B,
      simp only [and_imp, Set.mem_powerset, and_iff_right_iff_imp, ne.def, exists_imp_distrib, Set.mem_sep],
      intros X B hBA hBne hXB z hz, rw Set.mem_powerset, intros y hy, rw Set.mem_powerset, intros x hx,
      simp only [Set.mem_powerset, Set.mem_union], rw hXB at hz,
      simp only [Set.mem_prod, exists_prop, Set.mem_singleton] at hz,
      rcases hz with ⟨B', hBB', b, hb, hbp⟩, rw hbp at hy, simp only [Set.pair, Set.mem_insert, Set.mem_singleton] at hy,
      cases hy,
        rw [hy, Set.mem_singleton] at hx, right, rw [hx, hBB'], exact hBA,
      rw hy at hx, simp only [Set.mem_insert, Set.mem_singleton] at hx, cases hx,
        right, rw [hx, hBB'], exact hBA,
      left, simp only [hx, Set.mem_Union, exists_prop, Set.mem_powerset], exact ⟨_, hBA, hb⟩,
    have h𝓐' : ∀ a ∈ 𝓐, a ≠ ∅ ∧ ∀ b ∈ 𝓐, b ≠ a → a ∩ b = ∅, intros a ha,
      rw h𝓐 _ at ha, rcases ha with ⟨B, -, hBne, he⟩, split,
        apply ne_empty_of_inhabited, rw he,
        replace hBne := inhabited_of_ne_empty hBne, rcases hBne with ⟨b, hb⟩, use B.pair b,
        rw [Set.pair_mem_prod, Set.mem_singleton], exact ⟨rfl, hb⟩,
      intros b hb hba, rw eq_empty, intros z hz,
      rw h𝓐 _ at hb, rcases hb with ⟨B', -, hBne', he'⟩, apply hba, rw [he, he'],
      have hBB' : B = B',
        simp only [he, he', Set.mem_inter, Set.mem_prod, exists_prop, Set.mem_singleton] at hz,
        rcases hz with ⟨⟨x, hx, y, hy, hxy⟩, x', hx', y', hy', hxy'⟩, rw [←hx, ←hx'], rw hxy at hxy',
        exact (Set.pair_inj hxy').left,
      rw hBB',
    specialize ax4 h𝓐', rcases ax4 with ⟨C, hC⟩,
    let F := C ∩ 𝓐.Union, use F,
    have hFinto : F.into_fun {x ∈ A.powerset | x ≠ ∅} F.ran, rw Set.fun_def_equiv,
      have Fsubprod : F ⊆ {x ∈ A.powerset | x ≠ ∅}.prod F.ran,
        intros z hz, simp only [Set.mem_inter, Set.mem_Union, exists_prop] at hz,
        rcases hz with ⟨hzC, X, hX𝓐, hzX⟩, simp only [Set.mem_prod, exists_prop, Set.mem_ran, Set.mem_sep, Set.mem_inter, Set.mem_powerset],
        rw h𝓐 _ at hX𝓐, rcases hX𝓐 with ⟨B, hBA, hBne, hX⟩, refine ⟨_, ⟨hBA, hBne⟩, _⟩, rw hX at hzX,
        simp only [Set.mem_prod, exists_prop, Set.mem_singleton] at hzX, rcases hzX with ⟨B', hB', b, hb, he⟩,
        rw he at hzC, rw ←hB', refine ⟨_, ⟨_, hzC, _⟩, he⟩, simp only [Set.mem_Union, exists_prop, h𝓐 _],
        refine ⟨_, ⟨_, hBA, hBne, rfl⟩, _⟩, simp only [Set.pair_mem_prod, Set.mem_singleton], exact ⟨hB', hb⟩,
      refine ⟨Fsubprod, _⟩,
      intros B hB, simp only [Set.mem_sep, exists_prop, Set.mem_powerset] at hB, simp only [Set.mem_inter, Set.mem_Union],
      have hB𝓐 : Set.prod {B} B ∈ 𝓐, rw h𝓐 _, exact ⟨_, hB.left, hB.right, rfl⟩,
      have he : ∃ x, C ∩ Set.prod {B} B = {x}, apply hC _ hB𝓐,
      replace he : ∃! x, x ∈ C ∩ Set.prod {B} B, rcases he with ⟨x, he⟩, rw ←Set.ext_iff at he, simp only [Set.mem_singleton] at he,
        refine ⟨x, (he x).mpr rfl, λ x' hx, _⟩, apply (he x').mp, exact hx,
      simp only [Set.mem_inter, Set.mem_prod, exists_prop, Set.mem_singleton] at he,
      rcases he with ⟨x, ⟨hxC, B', hBB', b, hb, he⟩, ha⟩, rw [he, hBB'] at hxC, refine ⟨_, ⟨hxC, _, hB𝓐, _⟩, λ b' hb', _⟩,
        rw [Set.pair_mem_prod, Set.mem_singleton], exact ⟨rfl, hb⟩,
      rcases hb' with ⟨hxC', X, hX𝓐, he'⟩, rw h𝓐 X at hX𝓐, rcases hX𝓐 with ⟨B'', hBA'', hBne'', hB''⟩,
      refine (@Set.pair_inj B _ B _ _).right, rw [he, hBB'] at ha, apply ha _, refine ⟨hxC', _, rfl, b', _, rfl⟩,
      rw [hB'', Set.pair_mem_prod, Set.mem_singleton] at he', rw he'.left, exact he'.right,
    refine ⟨hFinto.left, hFinto.right.left, λ B hB, _⟩,
    rw Set.mem_dom at hB, rcases hB with ⟨b, hb⟩,
    have hb' : ∃ X, X ∈ 𝓐 ∧ B.pair b ∈ X, simp only [Set.mem_inter, Set.mem_Union, exists_prop] at hb, exact hb.right,
    rcases hb' with ⟨X, hX𝓐, hBX⟩, rw h𝓐 _ at hX𝓐, rcases hX𝓐 with ⟨B', hBA', hB', he⟩,
    simp only [he, Set.pair_mem_prod, exists_prop, Set.mem_singleton] at hBX, rw hBX.left,
    rw hBX.left at hb, rw Set.fun_value_def hFinto.left hb at hBX, exact hBX.right, },
  tfae_have : 3 → 1,
  { dsimp only [Axiom_of_choice_III, Axiom_of_choice_I], intros ax3 R hR, specialize @ax3 R.ran,
    rcases ax3 with ⟨G, Gfun, GsubR, hG⟩,
    let F := Set.pair_sep_eq R.dom G.ran (λ x, G.fun_value {y ∈ R.ran | x.pair y ∈ R}),
    have Ffun : F.is_function := Set.pair_sep_eq_is_fun,
    have BGdom : ∀ {a : Set}, a ∈ R.dom → {y ∈ R.ran | a.pair y ∈ R} ∈ G.dom, intros a ha,
        simp only [GsubR, Set.mem_sep, Set.mem_powerset], split,
          exact Set.sep_subset,
        apply ne_empty_of_inhabited, rw Set.mem_dom at ha, simp only [Set.inhab, Set.mem_sep, Set.mem_ran],
        rcases ha with ⟨b, hab⟩, exact ⟨b, ⟨a, hab⟩, hab⟩,
    refine ⟨_, Ffun, _, _⟩,
      intros z hz, simp only [F, Set.pair_sep_eq, Set.mem_pair_sep, exists_prop] at hz,
      rcases hz with ⟨a, ha, b, hb, he, he'⟩, subst he, subst he',
      specialize hG _ (BGdom ha), rw Set.mem_sep at hG, exact hG.right,
    apply Set.pair_sep_eq_dom_eq, intros a ha, apply Set.fun_value_def'' Gfun (BGdom ha), },
  tfae_finish,
end

theorem ax_ch_1 : Axiom_of_choice_I :=
begin
  refine list.tfae_prf choice_equiv _ _ @ax_ch_3, finish, finish,
end

theorem ax_ch_2 : Axiom_of_choice_II :=
begin
  refine list.tfae_prf choice_equiv _ _ @ax_ch_3, finish, finish,
end

lemma T3J_b {F A B : Set} (hf : F.into_fun A B) (hne : ∃ x, x ∈ A) : (∃ H : Set, H.into_fun B A ∧ F.comp H = B.id) ↔ F.onto_fun A B :=
begin
  rcases hf with ⟨hf, hd, hr⟩,
  split,
  { rintro ⟨H, ⟨hhf, hhd, hhr⟩, heq⟩,
    refine ⟨hf, hd, _⟩,
    apply Set.ext, intro z, split,
    { intro hz, exact hr hz, },
    { intro hz,
      rw Set.mem_ran, existsi H.fun_value z,
      apply Set.fun_value_def''' hf, rw hd,
      apply hhr, refine Set.fun_value_def'' hhf _, rw hhd, assumption,
      rw ←T3H_c hf hhf, rw heq, symmetry, exact Set.id_value hz,
      rw heq, rw Set.id_onto.right.left, assumption, }, },
  { rintro ⟨-, -, hre⟩,
    rcases @ax_ch_1 F.inv Set.inv_rel with ⟨H, hhf, hhs, hhd⟩,
    existsi H, split, refine ⟨hhf, _, _⟩,
      simp only [hhd, T3E_a, hre],
      rw ←hd, rw ←T3E_b, exact Set.ran_subset_of_subset hhs,
    apply Set.fun_ext (T3H_a hf hhf) Set.id_is_function,
      apply Set.ext, intro z,
      simp only [T3H_b hf hhf, Set.mem_sep, hhd, T3E_a, hre, Set.id_onto.right.left, and_iff_left_iff_imp],
      intro hz, simp only [←T3E_b], apply Set.ran_subset_of_subset hhs,
      apply Set.fun_value_def'' hhf, simp only [hhd, T3E_a, hre, hz],
    intros x hx, rw Set.id_value, rw T3H_c hf hhf hx, symmetry,
    apply Set.fun_value_def hf,
    rw ←Set.pair_mem_inv, apply hhs,
    apply Set.fun_value_def' hhf,
    simp only [T3H_b hf hhf, Set.mem_sep] at hx, finish,
    simp only [T3H_b hf hhf, Set.mem_sep] at hx, finish, },
end

def Set.img_fun_img (F 𝓐 : Set) : Set := {B ∈ F.ran.powerset | ∃ A ∈ 𝓐, B = F.img A}

@[simp]
lemma Set.mem_img_fun_img {F 𝓐 B : Set} : B ∈ F.img_fun_img 𝓐 ↔ ∃ A ∈ 𝓐, B = F.img A :=
begin
  simp only [Set.img_fun_img, Set.mem_sep, and_imp, exists_prop, Set.mem_powerset, and_iff_right_iff_imp, exists_imp_distrib],
  intros A hA hB y hy, rw hB at hy, simp only [Set.mem_ran, Set.mem_img] at *, finish,
end

theorem T3K_a {F 𝓐 : Set} : F.img 𝓐.Union = (F.img_fun_img 𝓐).Union :=
begin
  apply Set.ext, intro y, simp only [exists_prop, Set.mem_img_fun_img, Set.mem_img, Set.mem_Union], split,
  { rintro ⟨x, ⟨A, hA, hx⟩, hp⟩, refine ⟨F.img A, ⟨A, hA, rfl⟩, _⟩,
    simp only [Set.mem_img], exact ⟨_, hx, hp⟩, },
  { rintro ⟨B, ⟨A, hA, hB⟩, hy⟩, rw [hB, Set.mem_img] at hy, rcases hy with ⟨x, hx, hp⟩,
    exact ⟨_, ⟨_, hA, hx⟩, hp⟩, },
end

theorem T3K_b {F 𝓐 : Set} : F.img 𝓐.Inter ⊆ (F.img_fun_img 𝓐).Inter :=
begin
  intro y, simp only [and_imp, Set.mem_img, exists_imp_distrib, Set.inhab, exists_prop, Set.mem_img_fun_img, Set.mem_Inter],
  intros x A hA ha hp, refine ⟨⟨F.img A, _, hA, rfl⟩, (λ B X hX hB, _)⟩, rw [hB, Set.mem_img],
  exact ⟨_, ha _ hX, hp⟩,
end

theorem T3K_b_eq {F 𝓐 : Set} (hf : F.one_to_one) : F.img 𝓐.Inter = (F.img_fun_img 𝓐).Inter :=
begin
  rw Set.eq_iff_subset_and_subset, refine ⟨T3K_b, _⟩, intro y,
  simp only [Set.mem_Inter, Set.inhab, and_imp, exists_prop, Set.mem_img_fun_img, Set.mem_img, exists_imp_distrib],
  intros B A hA hB ha,
  have hy : y ∈ F.img A, exact ha _ _ hA rfl, rw Set.mem_img at hy, rcases hy with ⟨x, hx, hp⟩,
  refine ⟨_, ⟨⟨_, hA⟩, (λ X hX, _)⟩, hp⟩,
  have hy : y ∈ F.img X, exact ha _ _ hX rfl, rw Set.mem_img at hy, rcases hy with ⟨x', hx', hp'⟩,
  have he : x = x', refine unique_of_exists_unique (hf y _) hp hp', rw Set.mem_ran, exact ⟨_, hp⟩,
  rw he, assumption,
end

theorem T3K_c {F A B : Set} : F.img A \ F.img B ⊆ F.img (A \ B) :=
begin
  intro y, simp only [Set.mem_img, Set.mem_diff, not_exists, and_imp, not_and, exists_imp_distrib],
  intros x hx hp ha, exact ⟨_, ⟨hx, (λ h, ha _ h hp)⟩, hp⟩,
end

theorem T3K_c_eq {F A B : Set} (hf : F.one_to_one) : F.img A \ F.img B = F.img (A \ B) :=
begin
  rw Set.eq_iff_subset_and_subset, refine ⟨T3K_c, _⟩, intro y,
  simp only [not_exists, and_imp, not_and, Set.mem_diff, Set.mem_img, exists_imp_distrib],
  intros x hA hB hp, refine ⟨⟨_, hA, hp⟩, (λ x' hB' hp', _)⟩, apply hB,
  have he : x = x', refine unique_of_exists_unique (hf y _) hp hp', rw Set.mem_ran, exact ⟨_, hp⟩,
  rw he, assumption,
end

def Set.into_funs (X Y : Set) : Set := {f ∈ (X.prod Y).powerset | f.into_fun X Y}

@[simp]
lemma Set.mem_into_funs {X Y f : Set} : f ∈ X.into_funs Y ↔ f.into_fun X Y :=
begin
  simp only [Set.into_funs, Set.mem_powerset, and_iff_right_iff_imp, Set.mem_sep], rintros ⟨hf, hd, hr⟩ p hp,
  have hp' : ∃ x y : Set, p = x.pair y, from hf.left _ hp,
  rcases hp' with ⟨x, y, hp'⟩,
  simp *,
  have hd' : x ∈ f.dom, rw hp' at hp, simp, exact ⟨_, hp⟩,
  have hr' : y ∈ f.ran, rw hp' at hp, simp, exact ⟨_, hp⟩,
  rw hd at hd', refine ⟨hd', hr hr'⟩,
end

-- these examples are from the very end of the section on functions

theorem ex1 {A : Set} (h : A.inhab) : A.into_funs ∅ = ∅ :=
begin
  rw eq_empty, intros f hf, rw Set.mem_into_funs at hf, rcases h with ⟨x, hx⟩, rcases hf with ⟨hf, hd, hr⟩,
  rw ←hd at hx, rw Set.mem_dom at hx, rcases hx with ⟨y, hy⟩, apply (Set.mem_empty y), apply hr, rw Set.mem_ran,
  exact ⟨_, hy⟩,
end

theorem ex2 {A : Set} : (∅ : Set).into_funs A = {∅} :=
begin
  apply Set.ext, simp only [Set.mem_singleton, Set.mem_into_funs], intro f, split,
  { rintro ⟨⟨hre, hf⟩, hd, hr⟩, rw Set.eq_empty, intros p hp,
    have hx := hre _ hp,
    rcases hx with ⟨x, y, hx⟩, rw hx at hp, apply Set.mem_empty x, rw ←hd, rw Set.mem_dom, exact ⟨_, hp⟩, },
  { have hd : (∅ : Set).dom = ∅, rw Set.eq_empty, intros x hx, rw Set.mem_dom at hx, rcases hx with ⟨y, hy⟩,
      exact Set.mem_empty _ hy,
    intro he, rw he, refine ⟨⟨(λ p hp, _), (λ x hx, _)⟩, _, _⟩,
    { exfalso, exact p.mem_empty hp, },
    { rw hd at hx, exfalso, exact x.mem_empty hx, },
    { exact hd, },
    { intros y hy, rw Set.mem_ran at hy, rcases hy with ⟨y, hy⟩,
        exfalso, exact Set.mem_empty _ hy, }, },
end

theorem p16 : ¬ ∃ X : Set, ∀ f : Set, f ∈ X ↔ f.is_function :=
begin
  rintro ⟨X, hX⟩, apply univ_not_set, refine ⟨X.Union.Union.Union, (λ x, _)⟩,
  simp only [exists_prop, Set.mem_Union], refine ⟨{x}, ⟨x.pair x, ⟨{x.pair x}, _, _⟩, _⟩, _⟩,
  { rw hX, refine ⟨(λ p hp, _), (λ t ht, ⟨x, _, _⟩)⟩,
    { rw Set.mem_singleton at hp, rw hp, exact ⟨_, _, rfl⟩, },
    { change t.pair x ∈ {x.pair x}, rw Set.mem_singleton, rw Set.mem_dom at ht, rcases ht with ⟨y, hy⟩,
      rw Set.mem_singleton at hy, rw (Set.pair_inj hy).left, },
    { intros x' hx', rw Set.mem_singleton at hx', exact (Set.pair_inj hx').right, }, },
  { rw Set.mem_singleton, },
  { rw [Set.pair, Set.mem_pair], left, refl, },
  { rw Set.mem_singleton, },
end

-- Chapter 3, problem 17
theorem Set.comp_one_to_one {f : Set} (hf : f.one_to_one) {g : Set} (hg : g.one_to_one) : (f.comp g).one_to_one :=
begin
  intros y hy, rw [Set.mem_ran] at hy, apply exists_unique_of_exists_of_unique hy,
  intros x x' hx hx', rw [Set.pair_mem_comp] at hx hx',
  rcases hx with ⟨z, hxz, hzy⟩, rcases hx' with ⟨z', hxz', hzy'⟩,
  have hze : z = z', refine unique_of_exists_unique (hf _ _) hzy hzy', rw Set.mem_ran, finish,
  subst hze,
  refine unique_of_exists_unique (hg _ _) hxz hxz', rw Set.mem_ran, finish,
end

-- chapter 3, problem 21
theorem Set.comp_assoc {R S T : Set} : (R.comp S).comp T = R.comp (S.comp T) :=
begin
  apply Set.ext, simp only [Set.mem_comp, Set.pair_mem_comp], intro z, split,
  { rintro ⟨a, b, d, hz, hT, c, hS, hR⟩, exact ⟨a, c, d, hz, ⟨b, hT, hS⟩, hR⟩, },
  { rintro ⟨a, c, d, hz, ⟨b, hT, hS⟩, hR⟩, exact ⟨a, b, d, hz, hT, c, hS, hR⟩, },
end

section p30
parameters (A F : Set.{u})

def B : Set := {X ∈ A.powerset | F.fun_value X ⊆ X}.Inter
def C : Set := {X ∈ A.powerset | X ⊆ F.fun_value X}.Union

lemma F_sub_of_self (hf : F.into_fun A.powerset A.powerset) {X : Set} (h : X ∈ A.powerset) : F.fun_value X ∈ A.powerset :=
begin
  apply Set.ran_sub_of_into hf, apply Set.fun_value_def'' (Set.is_function_of_into hf),
  rw Set.dom_eq_of_into hf, assumption,
end

lemma C_subset_A : C ∈ A.powerset :=
begin
  rw Set.mem_powerset, intro z, simp only [C, Set.mem_Union, exists_prop, Set.mem_sep, Set.mem_powerset],
  rintro ⟨X, ⟨hX, -⟩, hz⟩, exact hX hz,
end

lemma B_subset_A (hf : F.into_fun A.powerset A.powerset) : B ∈ A.powerset :=
begin
  rw Set.mem_powerset, intro z, simp only [B, Set.mem_Inter, Set.mem_sep],
  rintro ⟨hin, ha⟩, apply ha, refine ⟨Set.mem_powerset_self, _⟩, rw ←Set.mem_powerset, apply F_sub_of_self hf,
  exact Set.mem_powerset_self,
end

lemma subset_C {X : Set} (hA : X ∈ A.powerset) (hX : X ⊆ F.fun_value X) : X ⊆ C :=
begin
  rw C, apply Set.subset_Union, rw [Set.mem_sep, Set.mem_powerset], finish,
end

lemma B_subset {X : Set} (hA : X ∈ A.powerset) (hX : F.fun_value X ⊆ X) : B ⊆ X :=
begin
  rw B, apply Set.subset_Inter, rw [Set.mem_sep, Set.mem_powerset], finish,
end

theorem p30_b {X : Set}
(hA : X ⊆ A)
(hX : F.fun_value X = X)
: B ⊆ X ∧ X ⊆ C :=
begin
  rw Set.eq_iff_subset_and_subset at hX, refine ⟨(λ x hx, _), (λ x hx, _)⟩,
  { rw B at hx, simp only [Set.mem_Inter, Set.mem_sep, Set.mem_powerset] at hx,
    apply hx.right, exact ⟨hA, hX.left⟩, },
  { rw C, simp only [Set.mem_Union, Set.mem_sep, Set.mem_powerset, exists_prop],
    exact ⟨_, ⟨hA, hX.right⟩, hx⟩, },
end

theorem p30_a {hf : F.into_fun A.powerset A.powerset}
{hmon : ∀ {X Y : Set}, X ⊆ Y → Y ∈ A.powerset → F.fun_value X ⊆ F.fun_value Y}
: F.fun_value B = B ∧ F.fun_value C = C :=
begin
  have hC : C ⊆ F.fun_value C, intros z hz,
    simp only [C, Set.mem_Union, exists_prop, Set.mem_sep] at hz,
    rcases hz with ⟨X, ⟨hA, hX⟩, hz⟩, exact hmon (subset_C hA hX) C_subset_A (hX hz),
  have hB : F.fun_value B ⊆ B, intros z hz,
    simp only [B, Set.mem_Inter, Set.mem_sep], refine ⟨⟨A, _⟩, (λ X ⟨hA, hX⟩, hX (hmon (B_subset hA hX) hA hz))⟩,
    simp only [Set.mem_sep], rw ←Set.mem_powerset, refine ⟨Set.mem_powerset_self, _⟩,
    apply F_sub_of_self hf, exact Set.mem_powerset_self,
  simp only [Set.eq_iff_subset_and_subset], refine ⟨⟨hB, _⟩, _, hC⟩,
  { apply B_subset, apply F_sub_of_self hf, exact B_subset_A hf, apply hmon hB (B_subset_A hf), },
  { apply subset_C, apply F_sub_of_self hf, exact C_subset_A, apply hmon hC, apply F_sub_of_self hf, exact C_subset_A, },
end
end p30

def Set.inf_prod (H I : Set) : Set
:= {f ∈ I.into_funs (H.img I).Union | f.is_function ∧ f.dom = I ∧ ∀ i : Set, i ∈ I → f.fun_value i ∈ H.fun_value i}

@[simp]
lemma Set.mem_inf_prod {H I f : Set} (hF : H.is_function) (hD : I ⊆ H.dom)
: f ∈ H.inf_prod I ↔ f.is_function ∧ f.dom = I ∧ ∀ i : Set, i ∈ I → f.fun_value i ∈ H.fun_value i :=
begin
  simp only [Set.inf_prod, Set.mem_sep, and_imp, Set.mem_fun_value, and_iff_right_iff_imp, Set.mem_into_funs],
  intros hf hd ha, refine ⟨hf, hd, (λ y hy, _)⟩, simp only [Set.mem_Union, exists_prop, Set.mem_img_fun_img],
  rw Set.mem_ran at hy, rcases hy with ⟨x, hy⟩,
  have hxi : x ∈ I, rw [←hd, Set.mem_dom], exact ⟨_, hy⟩,
  have hY := ha _ hxi, rcases hY with ⟨Y, hH, hY⟩,
  refine ⟨Y, _, _⟩,
  { simp only [Set.mem_img], refine ⟨x, hxi, hH⟩, },
  { rw Set.fun_value_def hf hy, assumption, },
end

theorem Set.inf_prod_inhab {H I : Set} (hF : H.is_function) (hD : H.dom = I) (hA : ∀ i : Set, i ∈ I → H.fun_value i ≠ ∅)
: (H.inf_prod I ).inhab :=
begin
  have hD' : I ⊆ H.dom, rw hD, exact Set.subset_self,
  simp only [Set.inhab, Set.mem_inf_prod hF hD'], exact @ax_ch_2 _ _ ⟨hF, hD, hA⟩,
end

def Set.symmetric (R : Set) : Prop := ∀ ⦃x y : Set⦄, x.pair y ∈ R → y.pair x ∈ R
def Set.transitive (R : Set) : Prop := ∀ ⦃x y z : Set⦄, x.pair y ∈ R → y.pair z ∈ R → x.pair z ∈ R

structure Set.equiv_rel (R A : Set) : Prop :=
(rel : R ⊆ A.prod A)
(refl : ∀ ⦃x : Set⦄, x ∈ A → x.pair x ∈ R)
(symm : R.symmetric)
(trans : R.transitive)

theorem T3M {R : Set} (hr : R.is_rel) (hs : R.symmetric) (ht : R.transitive) : R.equiv_rel R.fld :=
begin
  refine ⟨(λ p hp, _), _, hs, ht⟩,
  { have h : ∃ x y : Set, p = x.pair y := hr _ hp, rcases h with ⟨x, y, h⟩, rw h at hp,
    simp only [Set.mem_prod, exists_prop, Set.fld, Set.mem_union, Set.mem_dom, Set.mem_ran],
    exact ⟨_, or.inl ⟨_, hp⟩, _, or.inr ⟨_, hp⟩, h⟩, },
  have h : ∀ {x y : Set}, x.pair y ∈ R → x.pair x ∈ R,
    intros x y h, exact ht h (hs h),
  simp only [Set.fld, Set.mem_union, Set.mem_dom, Set.mem_ran], rintros x (⟨y, hp⟩|⟨y, hp⟩),
  { exact h hp, },
  { exact h (hs hp), },
end

def Set.eq_class (R x : Set) : Set := {t ∈ R.ran | x.pair t ∈ R}

@[simp]
lemma Set.mem_eq_class {R x t : Set} : t ∈ R.eq_class x ↔ x.pair t ∈ R :=
begin
  simp only [Set.eq_class, and_iff_right_iff_imp, Set.mem_ran, Set.mem_sep],
  intro h, exact ⟨_, h⟩,
end

lemma Set.mem_eq_class_of_self {R A x : Set} (hr : R.equiv_rel A) (hx : x ∈ A) : x ∈ R.eq_class x :=
begin
  rw Set.mem_eq_class, exact hr.refl hx,
end

def Set.eq_classes (R A : Set) : Set := {X ∈ R.ran.powerset | ∃ x : Set, X = R.eq_class x ∧ x ∈ A}

@[simp]
lemma Set.mem_eq_classes {R A X : Set} : X ∈ R.eq_classes A ↔ ∃ x : Set, X = R.eq_class x ∧ x ∈ A :=
begin
  simp only [Set.eq_classes, Set.mem_powerset, and_iff_right_iff_imp, exists_imp_distrib, Set.mem_sep],
  rintros x ⟨hX, hx⟩, rw hX, intro t, rw [Set.eq_class, Set.mem_sep], finish,
end

lemma L3N {R A : Set} (hr : R.equiv_rel A) {x y : Set} (hx : x ∈ A) (hy : y ∈ A)
: R.eq_class x = R.eq_class y ↔ x.pair y ∈ R :=
begin
  refine ⟨(λ h, _), (λ h, _)⟩,
  { rw [←Set.mem_eq_class, h, Set.mem_eq_class], exact hr.refl hy, },
  { apply Set.ext, intro t, simp only [Set.mem_eq_class], split,
    { exact (λ ht, hr.trans (hr.symm h) ht), },
    { exact (λ ht, hr.trans h ht), }, },
end

structure Set.partition (P A : Set) : Prop :=
(subs : ∀ ⦃x : Set⦄, x ∈ P → x ⊆ A)
(nonem : ∀ ⦃x : Set⦄, x ∈ P → x ≠ ∅)
(disj : ∀ ⦃x y : Set⦄, x ∈ P → y ∈ P → x ≠ y → (x ∩ y) = ∅)
(exhaust : ∀ ⦃x : Set⦄, x ∈ A → ∃ X : Set, X ∈ P ∧ x ∈ X)

theorem T3P {R A : Set} (hr : R.equiv_rel A) : (R.eq_classes A).partition A :=
begin
  refine ⟨_, _, _, _⟩,
  { simp only [Set.mem_eq_classes], rintros X ⟨x, hX⟩ t ht, simp only [hX, Set.mem_eq_class] at ht,
    replace ht : x.pair t ∈ A.prod A := hr.rel ht, simp only [Set.pair_mem_prod] at ht,
    exact ht.right },
  { simp only [Set.mem_eq_classes], rintros X ⟨x, hX, hx⟩, apply ne_empty_of_inhabited, existsi x,
    rw hX, exact Set.mem_eq_class_of_self hr hx, },
  { simp only [Set.mem_eq_classes], rintros X Y ⟨x, hX, hx⟩ ⟨y, hY, hy⟩ hne, rw Set.eq_empty,
    intros t ht, simp only [Set.mem_inter, hX, hY, Set.mem_eq_class] at ht,
    apply hne, rw [hX, hY, L3N hr hx hy], exact hr.trans ht.left (hr.symm ht.right), },
  { simp only [Set.mem_eq_classes], intros x hx, exact ⟨_, ⟨_, rfl, hx⟩, Set.mem_eq_class_of_self hr hx⟩, },
end

-- I'm not writing any lemmas for this unless we use it
def Set.natural_map (R A : Set) : Set := Set.pair_sep (λ x X, X = R.eq_class x) A (R.eq_classes A)

-- thm 3Q
--37
--38, maybe
--39, maybe
--42
--delay 3Q until it's needed

structure Set.lin_order (A R : Set) : Prop :=
(rel : R ⊆ A.prod A)
(trans : R.transitive)
(irrefl : ∀ ⦃x : Set⦄, x.pair x ∉ R)
(conn : ∀ ⦃x y : Set⦄, x ∈ A → y ∈ A → x ≠ y → x.pair y ∈ R ∨ y.pair x ∈ R)

lemma Set.prod_disj {A B C D : Set} (h : C ∩ D = ∅) : A.prod C ∩ B.prod D = ∅ :=
begin
  rw eq_empty, intros z hz, simp only [Set.mem_inter, Set.mem_prod, exists_prop] at hz,
  rcases hz with ⟨⟨a, ha, b, hb, he⟩, a', ha', b', hb', he'⟩,
  rw he' at he, rw (Set.pair_inj he).right at hb',
  have hb'' : b ∈ C ∩ D, rw Set.mem_inter, finish,
  rw h at hb'', exact Set.mem_empty _ hb'',
end

lemma Set.singleton_disj_of_ne {A B : Set} (hne : A ≠ B) : {A} ∩ {B} = (∅ : Set) :=
begin
  rw eq_empty, intros z hz, simp only [Set.mem_inter, Set.mem_singleton] at hz, apply hne, rw ←hz.left, rw ←hz.right,
end