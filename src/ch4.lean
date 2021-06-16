import ch3

universe u

namespace Set

def succ (a : Set) : Set := {a} ∪ a

@[simp]
lemma mem_succ {a b : Set} : b ∈ a.succ ↔ b = a ∨ b ∈ a :=
by rw [succ, mem_union, mem_singleton]

@[simp]
lemma insert_eq {x y : Set} : insert x y = {x} ∪ y :=
by simp only [←ext_iff, mem_insert, mem_union, mem_singleton, forall_const, iff_self]

@[simp]
lemma succ_eq_insert {a : Set} : a.succ = insert a a := by simp only [succ, insert_eq]

structure induct (A : Set) : Prop :=
(zero : ∅ ∈ A)
(succ_closed : ∀ ⦃a : Set⦄, a ∈ A → a.succ ∈ A)

-- Set.omega is the inductive set defined in mathlib
-- Set.omega_zero and Set.omega_succ says that it's inductive

theorem induct_omega : omega.induct :=
begin
  refine ⟨omega_zero, (λ a ha, _)⟩, simp only [succ_eq_insert, omega_succ ha],
end

-- The infinity axiom
theorem exists_inductive : ∃ A : Set, A.induct := ⟨_, induct_omega⟩

def is_nat (n : Set) : Prop := ∀ ⦃A : Set⦄, A.induct → n ∈ A

def nat : Set := {n ∈ omega | n.is_nat}

notation `ω` := nat

@[simp]
theorem mem_nat {n : Set} : n ∈ ω ↔ n.is_nat :=
begin
  simp only [nat, mem_sep, and_iff_right_iff_imp],
  intro hn, exact hn induct_omega,
end

-- theorem 4B part 1
theorem nat_induct : nat.induct :=
begin
  refine ⟨_, _⟩,
  { rw mem_nat, exact (λ A hA, hA.zero), },
  { intros a ha, rw mem_nat at ha, rw mem_nat,
    intros A hA, exact hA.succ_closed (ha hA), },
end

def one : Set := (∅ : Set).succ
def two : Set := one.succ
def three : Set := two.succ
def four : Set := three.succ

lemma zero_nat : ∅ ∈ ω := nat_induct.zero
lemma one_nat : one ∈ ω := nat_induct.succ_closed zero_nat
lemma two_nat : two ∈ ω := nat_induct.succ_closed one_nat
lemma three_nat : three ∈ ω := nat_induct.succ_closed two_nat
lemma four_nat : four ∈ ω := nat_induct.succ_closed three_nat

-- theorem 4B part 2
theorem nat_subset_induct {A : Set} (hA : A.induct) : ω ⊆ A := (λ a ha, mem_nat.mp ha hA)

-- induction principle
theorem eq_nat_of_induct_sub {A : Set} (ha : A.induct) (hs : A ⊆ ω) : A = ω :=
eq_iff_subset_and_subset.mpr ⟨hs, nat_subset_induct ha⟩

lemma induction {p : Set → Prop} (hz : p ∅) (hi : ∀ {a : Set}, a ∈ ω → p a → p a.succ) : ∀ {n : Set}, n ∈ ω → p n :=
begin
  let T : Set := {n ∈ ω | p n},
  have he : T = ω, refine eq_nat_of_induct_sub ⟨_, _⟩ sep_subset,
    { simp only [hz, mem_sep, and_true, nat_induct.zero], },
    { simp only [mem_sep], rintros a ⟨ha, hp⟩, exact ⟨nat_induct.succ_closed ha, hi ha hp⟩, },
  intros n hn, rw [←he, mem_sep] at hn, finish,
end

-- Theorem 4C
theorem exists_pred {n : Set} (h : n ∈ ω) : n = ∅ ∨ ∃ p : Set, p ∈ ω ∧ n = p.succ :=
begin
  refine induction _ _ h,
  { exact or.inl rfl, },
  { intros a ha hp, exact or.inr ⟨_, ha, rfl⟩, },
end

theorem exists_pred_of_ne_zero {n : Set} (hn : n ∈ ω) (hnz : n ≠ ∅) : ∃ p : Set, p ∈ ω ∧ n = p.succ :=
begin
  cases exists_pred hn,
  { contradiction, },
  { assumption, },
end

theorem succ_neq_empty {n : Set} : n.succ ≠ ∅ :=
begin
  intro he, apply mem_empty n,
  simp only [←he, mem_union, succ_eq_insert, insert_eq, true_or, eq_self_iff_true, mem_singleton],
end

def transitive_set (A : Set) : Prop := A.Union ⊆ A

lemma transitive_set_iff {A : Set} : A.transitive_set ↔ ∀ {x : Set}, x ∈ A → ∀ {y : Set}, y ∈ x → y ∈ A :=
begin
  simp only [transitive_set, subset_def, mem_Union, exists_prop], split,
    intros h x xA y yx, exact h ⟨_, xA, yx⟩,
  rintros h y ⟨x, xA, yx⟩, exact h xA yx,
end

lemma transitive_set_iff' {A : Set} : A.transitive_set ↔ ∀ {x : Set}, x ∈ A → x ⊆ A :=
begin
  simp only [subset_def, transitive_set_iff],
end

theorem T4E {A : Set} (ht : transitive_set A) : A.succ.Union = A :=
begin
  rw [succ, p21, Union_singleton], apply ext, intro z,
  replace ht : z ∈ A.Union → z ∈ A := (λ h, ht h),
  simp only [mem_union, or_iff_left_iff_imp], assumption,
end

-- T4F
theorem nat_transitive {n : Set} (hn : n ∈ ω) : n.transitive_set :=
begin
  refine induction _ _ hn,
  { intro x, simp only [mem_Union, mem_empty, forall_prop_of_false, exists_false, not_false_iff, exists_prop_of_false], },
  { intros a ha hp, rw [transitive_set, T4E hp, succ], intros x hx, rw [mem_union, mem_singleton], finish, },
end

theorem succ_inj {n m : Set} (hn : n ∈ ω) (hm : m ∈ ω) (he : n.succ = m.succ) : n = m :=
begin
  rw [←T4E (nat_transitive hn), ←T4E (nat_transitive hm), he],
end

structure Peano_sys :=
(N S e : Set)
(hf : S.into_fun N N)
(he : e ∈ N)
(hi : e ∉ S.ran)
(hii : S.one_to_one)
(hiii : ∀ A : Set, A ⊆ N → e ∈ A → S.img A ⊆ A → A = N)

def succ_fun : Set := pair_sep (λ x y, y = x.succ) ω ω

lemma succ_fun_into_fun : succ_fun.into_fun ω ω :=
begin
  have hd : succ_fun.dom = ω, apply ext, intro x,
    simp only [ext_iff, mem_dom, succ_fun, mem_pair_sep, exists_prop], split,
    { rintro ⟨y, a, ha, b, -, he, -⟩, rw (pair_inj he).left, assumption, },
    { intro hx, exact ⟨_, _, hx, _, nat_induct.succ_closed hx, rfl, rfl⟩, },
  refine ⟨⟨pair_sep_is_rel, _⟩, hd, _⟩,
  { rw hd, intros x hx, refine ⟨x.succ, _, _⟩,
    { simp only [succ_fun, mem_pair_sep, exists_prop], exact ⟨_, hx, _, nat_induct.succ_closed hx, rfl, rfl⟩, },
    { intros y hy, simp only [succ_fun, mem_pair_sep, exists_prop] at hy,
      rcases hy with ⟨a, ha, b, hb, hp, he⟩, rw [(pair_inj hp).left, (pair_inj hp).right], assumption, }, },
  { intros y hy, simp only [mem_ran, succ_fun, mem_pair_sep, exists_prop] at hy,
    rcases hy with ⟨x, a, ha, b, hb, hp, he⟩, rw (pair_inj hp).right, assumption, },
end

lemma succ_fun_value {n : Set} (hn : n ∈ ω) : n.succ = succ_fun.fun_value n :=
begin
  apply fun_value_def (is_function_of_into succ_fun_into_fun),
  simp only [succ_fun, mem_pair_sep, exists_prop],
  exact ⟨_, hn, _, nat_induct.succ_closed hn, rfl, rfl⟩,
end

lemma succ_not_onto : ∅ ∉ succ_fun.ran :=
begin
  intro hm, rw [mem_ran] at hm, rcases hm with ⟨x, hx⟩,
  have h : ∅ = succ_fun.fun_value x := fun_value_def (is_function_of_into succ_fun_into_fun) hx,
  rw ←succ_fun_value at h, exact succ_neq_empty h.symm,
  rw ←(dom_eq_of_into succ_fun_into_fun), rw mem_dom, exact ⟨_, hx⟩,
end

lemma succ_one_to_one : succ_fun.one_to_one :=
begin
  have hf : succ_fun.is_function := is_function_of_into succ_fun_into_fun,
  have hd : succ_fun.dom = ω := dom_eq_of_into succ_fun_into_fun,
  intros y hx, simp only [mem_ran] at hx, rcases hx with ⟨x, hx⟩, refine ⟨_, hx, _⟩,
  intros x' hx',
  have hhx : y = succ_fun.fun_value x := fun_value_def hf hx,
  have hhx' : y = succ_fun.fun_value x' := fun_value_def hf hx',
  rw hhx' at hhx, apply succ_inj,
  rw ←hd, rw mem_dom, exact ⟨_, hx'⟩,
  rw ←hd, rw mem_dom, exact ⟨_, hx⟩,
  rw succ_fun_value, rw succ_fun_value, assumption,
  rw ←hd, rw mem_dom, exact ⟨_, hx⟩,
  rw ←hd, rw mem_dom, exact ⟨_, hx'⟩, 
end

lemma succ_fun_ran : succ_fun.ran = ω \ {∅} :=
begin
  apply ext, simp only [mem_ran_iff succ_fun_into_fun.left, succ_fun_into_fun.right.left, mem_diff, mem_singleton], intros y, split,
    rintro ⟨n, hn, hy⟩, rw ←succ_fun_value hn at hy, subst hy, exact ⟨nat_induct.succ_closed hn, succ_neq_empty⟩,
  rintro ⟨hy, hyne⟩,
  obtain ⟨x, hx, hxy⟩ := exists_pred_of_ne_zero hy hyne,
  refine ⟨_, hx, _⟩, subst hxy, rw succ_fun_value hx,
end

-- Theorem 4D
theorem exists_Peano_sys : Peano_sys :=
begin
  have hf : succ_fun.is_function := is_function_of_into succ_fun_into_fun,
  have hd : succ_fun.dom = ω := dom_eq_of_into succ_fun_into_fun,
  refine ⟨ω, succ_fun, ∅, succ_fun_into_fun, nat_induct.zero, succ_not_onto, succ_one_to_one, _⟩,
  { intros A hA hem hcl, refine eq_nat_of_induct_sub ⟨hem, _⟩ hA,
    intros a ha, apply hcl, rw mem_img, refine ⟨_, ha, _⟩, apply fun_value_def''' hf,
      rw dom_eq_of_into succ_fun_into_fun, apply hA, exact ha,
    exact succ_fun_value (hA ha), },
end

theorem nat_transitive_set : (ω : Set).transitive_set :=
begin
  suffices h : ∀ n ∈ ω, n ⊆ ω,
    intro X, simp only [mem_Union, exists_prop], rintros ⟨x, hx, hX⟩,
    apply h _ hx hX,
  intros n hn, refine @induction (λ x, x ⊆ ω) (λ x hx, _) _ _ hn,
  { exfalso, exact mem_empty _ hx, },
  { intros a ha hp, intro z, simp only [succ, mem_union, mem_singleton],
    rintro (h|h),
    { rw h, finish, },
    { exact hp h, }, },
end

structure acceptable (A a F v : Set) : Prop :=
(hf : v.is_function)
(hd : v.dom ⊆ ω)
(hr : v.ran ⊆ A)
(hi : ∅ ∈ v.dom → v.fun_value ∅ = a)
(hii : ∀ {n : Set}, n ∈ ω → n.succ ∈ v.dom → n ∈ v.dom ∧ v.fun_value n.succ = F.fun_value (v.fun_value n))

-- The domain is nat.
-- The range is a subset of A.
-- rec_fun (0) = a.
-- rec_fun (succ(n)) = F(rec_fun(n)).
-- so F : A → A
def rec_fun (A a F : Set) : Set :=
{v ∈ ((ω : Set).prod A).powerset | A.acceptable a F v}.Union

@[simp]
lemma mem_rec_fun {A a F p : Set} : p ∈ A.rec_fun a F ↔ ∃ v : Set, A.acceptable a F v ∧ p ∈ v :=
begin
  simp only [rec_fun, mem_Union, exists_prop, mem_sep, mem_powerset, and_assoc], split,
  { rintro ⟨v, hs, ha⟩, exact ⟨_, ha⟩, },
  { rintro ⟨v, ha, hm⟩, refine ⟨_, _, ha, hm⟩, intros q hq, simp only [mem_prod, exists_prop],
    have h : ∃ x y : Set, q = x.pair y := ha.hf.left _ hq,
    rcases h with ⟨x, y, hq⟩, refine ⟨_, _, _, _, hq⟩,
    { apply ha.hd, rw mem_dom, existsi y, rw ←hq, assumption, },
    { apply ha.hr, rw mem_ran, existsi x, rw ←hq, assumption, }, },
end

lemma rec_fun_rel {A a F : Set} (ha : a ∈ A) : (A.rec_fun a F).is_rel :=
begin
  intros p hp, rw mem_rec_fun at hp, rcases hp with ⟨v, ha, hp⟩, exact ha.hf.left _ hp,
end

lemma rec_fun_dom {A a F : Set} : (A.rec_fun a F).dom ⊆ ω :=
begin
  intros x hx, simp only [mem_dom, mem_rec_fun] at hx,
  rcases hx with ⟨y, v, ha, hx⟩, apply ha.hd, rw mem_dom, exact ⟨_, hx⟩,
end

@[simp]
lemma pair_mem_rec_fun {A a F x y : Set} : x.pair y ∈ A.rec_fun a F ↔ ∃ v : Set, A.acceptable a F v ∧ x.pair y ∈ v :=
begin
  simp only [mem_rec_fun],
end

lemma rec_fun_is_fun {A a F : Set} (ha : a ∈ A) : (A.rec_fun a F).is_function :=
begin
  refine ⟨_, _⟩,
  { exact rec_fun_rel ha, },
  { have hi : ∀ x : Set, x.mem (ω : Set) → ∀ y y' : Set, x.pair y ∈ (A.rec_fun a F) → x.pair y' ∈ (A.rec_fun a F) → y = y',
      intro x, refine @induction _ _ _ x, intros y y' hy hy',
      { simp only [pair_mem_rec_fun] at hy hy',
        rcases hy with ⟨v, hv, hy⟩,
        rcases hy' with ⟨v', hv', hy'⟩,
        have hd : ∅ ∈ v.dom, rw mem_dom, exact ⟨_, hy⟩,
        have hd' : ∅ ∈ v'.dom, rw mem_dom, exact ⟨_, hy'⟩,
        rw [fun_value_def hv.hf hy, fun_value_def hv'.hf hy', hv.hi hd, hv'.hi hd'], },
      { intros x hx hi y y' hy hy', simp only [pair_mem_rec_fun] at hy hy',
        rcases hy with ⟨v, hv, hy⟩,
        rcases hy' with ⟨v', hv', hy'⟩,
        have hd : x.succ ∈ v.dom, rw mem_dom, exact ⟨_, hy⟩,
        have hd' : x.succ ∈ v'.dom, rw mem_dom, exact ⟨_, hy'⟩,
        rw [fun_value_def hv.hf hy, fun_value_def hv'.hf hy', (hv.hii hx hd).right, (hv'.hii hx hd').right],
        have h : v.fun_value x = v'.fun_value x, apply hi,
          rw pair_mem_rec_fun, refine ⟨_, hv, fun_value_def' hv.hf (hv.hii hx hd).left⟩,
          rw pair_mem_rec_fun, refine ⟨_, hv', fun_value_def' hv'.hf (hv'.hii hx hd').left⟩,
        rw h, },
    intros x hx, refine exists_unique_of_exists_of_unique _ (hi x (rec_fun_dom hx)),
    rw mem_dom at hx, exact hx,
  },
end

lemma rec_fun_ran {A a F : Set} : (A.rec_fun a F).ran ⊆ A :=
begin
  intros y hy, simp only [mem_ran, pair_mem_rec_fun] at hy, rcases hy with ⟨x, v, hv, hy⟩,
  apply hv.hr, rw mem_ran, exact ⟨_, hy⟩,
end

lemma rec_fun_acceptable {A a F : Set} (ha : a ∈ A) : A.acceptable a F (A.rec_fun a F) :=
begin
  refine ⟨rec_fun_is_fun ha, rec_fun_dom, rec_fun_ran, _, _⟩,
  { intro h, simp only [mem_dom, pair_mem_rec_fun] at h, rcases h with ⟨y, v, hv, hy⟩,
    suffices h : (A.rec_fun a F).fun_value ∅ = v.fun_value ∅,
      rw h, refine hv.hi _, rw mem_dom, exact ⟨_, hy⟩,
    symmetry, refine fun_value_def (rec_fun_is_fun ha) _,
    rw pair_mem_rec_fun, refine ⟨_, hv, _⟩, refine fun_value_def' hv.hf _,
    rw mem_dom, exact ⟨_, hy⟩, },
  { intros x hx hd, simp only [mem_dom, pair_mem_rec_fun] at hd, rcases hd with ⟨y, v, hv, hy⟩,
    suffices h : (A.rec_fun a F).fun_value x.succ = v.fun_value x.succ,
      have hd : x ∈ v.dom, refine (hv.hii hx _).left, rw mem_dom, exact ⟨_, hy⟩,
      have hy' : x.succ ∈ v.dom, rw mem_dom, exact ⟨_, hy⟩,
      rw [h, (hv.hii hx hy').right],
      suffices h' : v.fun_value x = (A.rec_fun a F).fun_value x,
        rw h', refine ⟨_, rfl⟩, simp only [mem_dom, pair_mem_rec_fun], rw mem_dom at hd, rcases hd with ⟨y', hy''⟩,
        exact ⟨_, _, hv, hy''⟩,
      refine fun_value_def (rec_fun_is_fun ha) _, rw pair_mem_rec_fun,
      refine ⟨_, hv, _⟩, refine fun_value_def' hv.hf _, assumption,
    symmetry, refine fun_value_def (rec_fun_is_fun ha) _, rw pair_mem_rec_fun,
    refine ⟨_, hv, _⟩, refine fun_value_def' hv.hf _, rw mem_dom, exact ⟨_, hy⟩, },
end

lemma rec_fun_dom_eq_nat {A a F : Set} (ha : a ∈ A) (hF : F.into_fun A A) : (A.rec_fun a F).dom = ω :=
begin
  have hb : ∃ v : Set, A.acceptable a F v ∧ (∅ : Set).pair a ∈ v,
    refine ⟨{(∅ : Set).pair a}, _, mem_singleton.mpr rfl⟩,
    have hf : Set.is_function {(∅ : Set).pair a},
      simp only [is_function_iff, is_rel, mem_singleton], refine ⟨(λ p hp, ⟨_, _, by rw hp⟩), _⟩,
      intros x y y' he he', rw ←he' at he, exact (pair_inj he).right,
    split,
    { exact hf, },
    { intros x hx, simp only [mem_dom, mem_singleton] at hx, rcases hx with ⟨y, he⟩,
      rw (pair_inj he).left, exact nat_induct.zero, },
    { intros y hy, simp only [mem_ran, mem_singleton] at hy, rcases hy with ⟨x, he⟩,
      rw (pair_inj he).right, assumption, },
    { intro h, symmetry, refine fun_value_def hf _, rw mem_singleton, },
    { intros n hn hd, simp only [mem_dom, mem_singleton] at hd, rcases hd with ⟨y, hy⟩,
      exfalso, exact succ_neq_empty (pair_inj hy).left, },
  refine eq_nat_of_induct_sub _ rec_fun_dom, refine ⟨_, _⟩,
  { simp only [mem_dom, pair_mem_rec_fun], exact ⟨a, hb⟩, },
  { intros k hk,
    let h := A.rec_fun a F,
    let v := h ∪ {k.succ.pair (F.fun_value (h.fun_value k))},
    by_cases hc : k.succ ∈ h.dom,
      assumption,
    have hf : v.is_function, rw is_function_iff, split,
      { intros p hp, simp only [mem_union, mem_singleton] at hp, cases hp,
        { exact rec_fun_rel ha _ hp, },
        { exact ⟨_, _, hp⟩, }, },
      { simp only [mem_union, mem_singleton],
        rintros x y y' (hh|he) (hh'|he'),
        { rw [fun_value_def (rec_fun_is_fun ha) hh, fun_value_def (rec_fun_is_fun ha) hh'], },
        { rw [(pair_inj he').right, fun_value_def (rec_fun_is_fun ha) hh, (pair_inj he').left],
          have h : h.fun_value k.succ = F.fun_value (h.fun_value k),
            refine ((rec_fun_acceptable ha).hii _ _).right,
            { exact (rec_fun_acceptable ha).hd hk, },
            { simp only [←(pair_inj he').left, mem_dom], exact ⟨_, hh⟩, },
          rw h, },
        { rw [(pair_inj he).right, fun_value_def (rec_fun_is_fun ha) hh', (pair_inj he).left],
          have h : h.fun_value k.succ = F.fun_value (h.fun_value k),
            refine ((rec_fun_acceptable ha).hii _ _).right,
            { exact (rec_fun_acceptable ha).hd hk, },
            { simp only [←(pair_inj he).left, mem_dom], exact ⟨_, hh'⟩, },
          rw h, },
        { rw [(pair_inj he).right, (pair_inj he').right], }, },
    have hd : v.dom ⊆ ω, intros x hx,
      simp only [mem_dom, mem_union, mem_singleton] at hx,
      rcases hx with ⟨y, hx|hx⟩,
      { apply (rec_fun_acceptable ha).hd, rw mem_dom, exact ⟨_, hx⟩, },
      { rw (pair_inj hx).left, exact nat_induct.succ_closed ((rec_fun_acceptable ha).hd hk), },
    have hr : v.ran ⊆ A, refine (λ y hy, _),
      simp only [mem_ran, mem_union, mem_singleton] at hy, rcases hy with ⟨x, hy|hy⟩,
      { apply (rec_fun_acceptable ha).hr, rw mem_ran, exact ⟨_, hy⟩, },
      { rw (pair_inj hy).right, apply ran_sub_of_into hF,
        refine fun_value_def'' (is_function_of_into hF) _,
        rw dom_eq_of_into hF, apply (rec_fun_acceptable ha).hr,
        refine fun_value_def'' (rec_fun_acceptable ha).hf _, assumption, },
    have hva : A.acceptable a F v, refine ⟨hf, hd, hr, _, _⟩,
      { intro hz, symmetry, apply fun_value_def hf, rw [mem_union, mem_singleton, pair_mem_rec_fun],
        exact or.inl hb, },
      { intros n hn hdn, by_cases he : n.succ = k.succ,
        { have he' : n = k, exact succ_inj hn ((rec_fun_acceptable ha).hd hk) he,
          simp only [mem_dom, mem_union], refine ⟨⟨h.fun_value n, or.inl _⟩, _⟩,
          { apply fun_value_def' (rec_fun_acceptable ha).hf, rw he', assumption, },
          { rw he', symmetry, apply fun_value_def hf, rw mem_union, right,
            rw mem_singleton,
            suffices he'' : v.fun_value k = h.fun_value k, rw he'',
            symmetry, apply fun_value_def hf, rw mem_union, left,
            apply fun_value_def' (rec_fun_acceptable ha).hf, assumption, }, },
        { have hsn : n.succ ∈ h.dom, simp only [mem_dom, mem_union, mem_singleton] at hdn, rw mem_dom,
            rcases hdn with ⟨y, hy|hy⟩,
            { exact ⟨_, hy⟩, },
            { exfalso, exact he (pair_inj hy).left, },
          have hsn' : n ∈ v.dom, simp only [mem_dom, mem_union],
            suffices h : n ∈ h.dom, rw mem_dom at h, rcases h with ⟨y, hy⟩,
              exact ⟨_, or.inl hy⟩,
            exact ((rec_fun_acceptable ha).hii hn hsn).left,
          refine ⟨hsn', _⟩,
          have he' : v.fun_value n.succ = h.fun_value n.succ,
            symmetry, apply fun_value_def hf, rw mem_union, left,
            apply fun_value_def' (rec_fun_acceptable ha).hf, exact hsn,
          rw he', rw ((rec_fun_acceptable ha).hii hn hsn).right,
          have he'' : v.fun_value n = h.fun_value n,
            symmetry, apply fun_value_def hf, rw mem_union, left,
            apply fun_value_def' (rec_fun_acceptable ha).hf,
            exact ((rec_fun_acceptable ha).hii hn hsn).left,
          rw he'', }, },
    simp only [mem_dom, pair_mem_rec_fun], refine ⟨F.fun_value (h.fun_value k), _, hva, _⟩,
    simp only [mem_union, mem_singleton], right, refl, },
end

lemma rec_fun_into_fun {A a F : Set} (ha : a ∈ A) (hF : F.into_fun A A) : (A.rec_fun a F).into_fun ω A :=
⟨rec_fun_is_fun ha, rec_fun_dom_eq_nat ha hF, rec_fun_ran⟩

-- lemma rec_fun_unique {A a F : Set} : ∃! h : Set, h.fun_value ∅ = a
-- ∧ ∀ n : Set, n ∈ ω → h.fun_value n.succ = F.fun_value (h.fun_value n) :=
-- begin
-- end

theorem recursion_thm {A a F : Set} (ha : a ∈ A) (hF : F.into_fun A A) :
(A.rec_fun a F).fun_value ∅ = a
∧ ∀ n : Set, n ∈ ω → (A.rec_fun a F).fun_value n.succ = F.fun_value ((A.rec_fun a F).fun_value n) :=
begin
  split,
  { apply (rec_fun_acceptable ha).hi, rw rec_fun_dom_eq_nat ha hF, exact nat_induct.zero, },
  { intros n hn, apply ((rec_fun_acceptable ha).hii hn _).right,
    rw rec_fun_dom_eq_nat ha hF, exact nat_induct.succ_closed hn, },
end

def Piso (P : Peano_sys) : Set := P.N.rec_fun P.e P.S

-- Theorem 4H
theorem peano_isomorphic {P : Peano_sys} :
(Piso P).onto_fun ω P.N
∧ (Piso P).one_to_one
∧ (Piso P).fun_value ∅ = P.e
∧ ∀ n : Set, n ∈ ω → (Piso P).fun_value (succ_fun.fun_value n) = P.S.fun_value ((Piso P).fun_value n) :=
begin
  refine ⟨_, _, _, _⟩,
  { apply onto_of_into,
    { exact rec_fun_into_fun P.he P.hf, },
    { apply P.hiii _ rec_fun_ran,
      { change P.e ∈ (Piso P).ran, rw ←(recursion_thm P.he P.hf).left,
        change (Piso P).fun_value ∅ ∈ (Piso P).ran, apply fun_value_def'' (rec_fun_is_fun P.he),
        rw rec_fun_dom_eq_nat P.he P.hf, exact nat_induct.zero, },
      { intros y hy, simp only [mem_img, mem_ran] at hy, rcases hy with ⟨m, ⟨n, hh⟩, hS⟩,
        rw fun_value_def (is_function_of_into P.hf) hS,
        rw fun_value_def (rec_fun_is_fun P.he) hh,
        have hn : n.mem ω, rw ←rec_fun_dom_eq_nat P.he P.hf, change n ∈ (Piso P).dom, rw mem_dom, exact ⟨_, hh⟩,
        rw ←(recursion_thm P.he P.hf).right _ hn, apply fun_value_def'' (rec_fun_is_fun P.he),
        rw rec_fun_dom_eq_nat P.he P.hf, apply nat_induct.succ_closed hn, }, }, },
  { apply one_to_one_of (rec_fun_is_fun P.he), rw rec_fun_dom_eq_nat P.he P.hf,
    intros m hm, refine induction _ _ hm,
    { intros n hn hne,
      rcases exists_pred_of_ne_zero hn hne.symm with ⟨p, hp, he⟩,
      rw [(recursion_thm P.he P.hf).left, he, (recursion_thm P.he P.hf).right _ hp],
      intro he', apply P.hi, rw he', apply fun_value_def'' (is_function_of_into P.hf),
      rw dom_eq_of_into P.hf, apply @rec_fun_ran _ P.e P.S, apply fun_value_def'' (rec_fun_is_fun P.he),
      rw rec_fun_dom_eq_nat P.he P.hf, assumption, },
    { intros k hk hi n hn hne he,
      have h : n ≠ ∅, intro he', rw [he', (recursion_thm P.he P.hf).left, (recursion_thm P.he P.hf).right] at he,
        apply P.hi, rw ←he, apply fun_value_def'' (is_function_of_into P.hf),
        rw dom_eq_of_into P.hf, apply @rec_fun_ran _ P.e P.S, apply fun_value_def'' (rec_fun_is_fun P.he),
        rw rec_fun_dom_eq_nat P.he P.hf, assumption, assumption,
      rcases exists_pred_of_ne_zero hn h with ⟨p, hp, he'⟩, subst he', apply hne,
      rw [(recursion_thm P.he P.hf).right _ hk, (recursion_thm P.he P.hf).right _ hp] at he,
      have he' : k = p, apply classical.by_contradiction, intro hne', apply hi hp, assumption,
        apply from_one_to_one (is_function_of_into P.hf) P.hii,
        { rw dom_eq_of_into P.hf, apply rec_fun_ran, apply fun_value_def'' (rec_fun_is_fun P.he),
          rw rec_fun_dom_eq_nat P.he P.hf, assumption, },
        { rw dom_eq_of_into P.hf, apply rec_fun_ran, apply fun_value_def'' (rec_fun_is_fun P.he),
          rw rec_fun_dom_eq_nat P.he P.hf, assumption, },
        { assumption, },
      rw he', }, },
  { exact (recursion_thm P.he P.hf).left, },
  { intros n hn, rw ←succ_fun_value hn, exact (recursion_thm P.he P.hf).right _ hn, },
end

def pre_add (m : Set) : Set := (ω : Set).rec_fun m succ_fun
def add : Set := pair_sep_eq ((ω : Set).prod ω) ω (λ a, (pre_add a.fst).fun_value a.snd)
instance : has_add Set := ⟨λ m n, add.fun_value (m.pair n)⟩

lemma add_eq {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) : m + n = (pre_add m).fun_value n :=
begin
  let f : Set → Set := λ p, (pre_add p.fst).fun_value p.snd,
  have hf : f (m.pair n) = (pre_add m).fun_value n, simp only [f], rw [fst_congr, snd_congr],
  change add.fun_value (m.pair n) = (pre_add m).fun_value n, rw ←hf, apply pair_sep_eq_fun_value,
  have hd : add.dom = ((ω : Set).prod ω), apply pair_sep_eq_dom_eq, intros a ha, apply rec_fun_ran,
    apply fun_value_def'',
    { apply rec_fun_is_fun, exact (fst_snd_mem_dom_ran ha).left, },
    { rw [pre_add, rec_fun_dom_eq_nat],
      { exact (fst_snd_mem_dom_ran ha).right, },
      { exact (fst_snd_mem_dom_ran ha).left, },
      { exact succ_fun_into_fun, }, },
  rw [←add, hd, pair_mem_prod], exact ⟨hm, hn⟩,
end

-- Theorem 4I part A1
theorem add_base {m : Set} (hm : m ∈ ω) : m + ∅ = m :=
begin
  rw add_eq hm nat_induct.zero, exact (recursion_thm hm succ_fun_into_fun).left,
end
-- Theorem 4I part A2
theorem add_ind {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) : m + n.succ = (m + n).succ :=
begin
  rw [add_eq hm (nat_induct.succ_closed hn), add_eq hm hn], rw [pre_add, (recursion_thm hm succ_fun_into_fun).right _ hn],
  symmetry, refine succ_fun_value _, apply rec_fun_ran, apply fun_value_def'' (rec_fun_is_fun hm),
  rw rec_fun_dom_eq_nat hm succ_fun_into_fun, exact hn,
end

theorem add_into_nat {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) : m + n ∈ ω :=
begin
  revert n, apply induction,
  { rw add_base hm, exact hm, },
  { intros n hn hi, rw [add_ind hm hn], exact nat_induct.succ_closed hi, },
end

-- Theorem 4K
theorem add_assoc {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) {p : Set} (hp : p ∈ ω) : m + (n + p) = (m + n) + p :=
begin
  revert p, apply induction,
  { rw [add_base hn, add_base], exact add_into_nat hm hn, },
  { intros p hp hi, rw [add_ind hn hp, add_ind hm (add_into_nat hn hp), hi, add_ind (add_into_nat hm hn) hp], },
end

theorem zero_add {n : Set} (hn : n ∈ ω) : ∅ + n = n :=
begin
  revert n, apply induction,
  { rw add_base nat_induct.zero, },
  { intros n hn hi, rw [add_ind nat_induct.zero hn, hi], },
end

theorem succ_add {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) : m.succ + n = (m + n).succ :=
begin
  revert n, apply induction,
  { rw [add_base hm, add_base (nat_induct.succ_closed hm)], },
  { intros n hn hi, rw [add_ind (nat_induct.succ_closed hm) hn, hi, add_ind hm hn], },
end

theorem add_comm {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) : m + n = n + m :=
begin
  revert m, apply induction,
  { rw [add_base hn, zero_add hn], },
  { intros m hm hi, rw [succ_add hm hn, hi, add_ind hn hm], },
end

theorem succ_eq_add_one {n : Set} (hn : n ∈ ω) : n.succ = n + one :=
by rw [one, add_ind hn zero_nat, add_base hn]

def pre_mul (m : Set) : Set := (ω : Set).rec_fun ∅ (pre_add m)
def mul : Set := pair_sep_eq ((ω : Set).prod ω) ω (λ a, (pre_mul a.fst).fun_value a.snd)
instance : has_mul Set := ⟨λ m n, mul.fun_value (m.pair n)⟩

lemma pre_add_into_fun {m : Set} (hm : m ∈ ω) : m.pre_add.into_fun ω ω := rec_fun_into_fun hm succ_fun_into_fun

lemma mul_eq {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) : m * n = (pre_mul m).fun_value n :=
begin
  let f : Set → Set := λ p, (pre_mul p.fst).fun_value p.snd,
  have hf : f (m.pair n) = (pre_mul m).fun_value n, simp only [f], rw [fst_congr, snd_congr],
  change mul.fun_value (m.pair n) = (pre_mul m).fun_value n, rw ←hf, apply pair_sep_eq_fun_value,
  have hd : mul.dom = ((ω : Set).prod ω), apply pair_sep_eq_dom_eq, intros a ha, apply rec_fun_ran,
    apply fun_value_def'',
    { apply rec_fun_is_fun, exact nat_induct.zero, },
    { rw [pre_mul, rec_fun_dom_eq_nat],
      { exact (fst_snd_mem_dom_ran ha).right, },
      { exact nat_induct.zero, },
      { apply pre_add_into_fun (fst_snd_mem_dom_ran ha).left, }, },
  rw [←mul, hd, pair_mem_prod], exact ⟨hm, hn⟩,
end

-- Theorem 4J part M1
theorem mul_base {m : Set} (hm : m ∈ ω) : m * ∅ = ∅ :=
begin
  rw [mul_eq hm nat_induct.zero, pre_mul], refine (recursion_thm nat_induct.zero  (pre_add_into_fun hm)).left,
end
-- Theorem 4J part M2
theorem mul_ind {m : Set} (hm : m ∈ (ω : Set.{u})) {n : Set} (hn : n ∈ ω) : m * n.succ = m * n + m :=
begin
  rw [mul_eq hm (nat_induct.succ_closed hn), mul_eq hm hn],
  rw [pre_mul, (recursion_thm nat_induct.zero (pre_add_into_fun hm)).right _ hn],
  have h : ((ω : Set).rec_fun ∅ m.pre_add).fun_value n ∈ (ω : Set.{u}),
    apply rec_fun_ran, apply fun_value_def'' (rec_fun_is_fun nat_induct.zero),
    rw rec_fun_dom_eq_nat nat_induct.zero (pre_add_into_fun hm), exact hn,
  rw add_comm h hm,
  rw add_eq hm h,
end

theorem mul_into_nat {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) : m * n ∈ ω :=
begin
  revert n, apply induction,
  { rw [mul_base hm], exact nat_induct.zero, },
  { intros n hn hi, rw [mul_ind hm hn], exact add_into_nat hi hm, },
end

-- Theorem 4K
theorem mul_add {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) {p : Set} (hp : p ∈ ω) : m * (n + p) = m * n + m * p :=
begin
  revert p, apply induction,
  { rw [add_base hn, mul_base hm, add_base (mul_into_nat hm hn)], },
  { intros p hp hi, rw [add_ind hn hp, mul_ind hm (add_into_nat hn hp), hi, ←add_assoc (mul_into_nat hm hn) (mul_into_nat hm hp) hm, mul_ind hm hp], },
end

theorem mul_assoc {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) {p : Set} (hp : p ∈ ω) : m * (n * p) = (m * n) * p :=
begin
  revert p, apply induction,
  { rw [mul_base hn, mul_base hm, mul_base (mul_into_nat hm hn)], },
  { intros p hp hi, rw [mul_ind hn hp, mul_add hm (mul_into_nat hn hp) hn, hi, mul_ind (mul_into_nat hm hn) hp], },
end

theorem zero_mul {n : Set} (hn : n ∈ ω) : ∅ * n = ∅ :=
begin
  revert n, apply induction,
  { rw [mul_base nat_induct.zero], },
  { intros n hn hi, rw [mul_ind nat_induct.zero hn, hi, add_base nat_induct.zero], },
end

theorem succ_mul {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) : m.succ * n = m * n + n :=
begin
  revert n, apply induction,
  { rw [mul_base (nat_induct.succ_closed hm), mul_base hm, add_base nat_induct.zero], },
  { intros n hn hi, rw [mul_ind (nat_induct.succ_closed hm) hn, add_ind (mul_into_nat (nat_induct.succ_closed hm) hn) hm, hi],
    rw [←add_assoc (mul_into_nat hm hn) hn hm, add_comm hn hm, add_assoc (mul_into_nat hm hn) hm hn],
    rw [add_ind (mul_into_nat hm (nat_induct.succ_closed hn)) hn, mul_ind hm hn], },
end

theorem mul_comm {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) : m * n = n * m :=
begin
  revert m, apply induction,
  { rw [mul_base hn, zero_mul hn], },
  { intros m hm hi, rw [succ_mul hm hn, hi, mul_ind hn hm], },
end

theorem mul_one {m : Set} (hm : m ∈ ω) : m * one = m :=
begin
  revert m, apply induction,
  { rw zero_mul one_nat, },
  { intros m hm hi, rw [succ_mul hm one_nat, hi, succ_eq_add_one hm], },
end

theorem one_mul {m : Set} (hm : m ∈ ω) : one * m = m :=
begin
  rw mul_comm one_nat hm, exact mul_one hm,
end

def pre_exp (m : Set) : Set := (ω : Set).rec_fun one (pre_mul m)
def exp : Set := pair_sep_eq ((ω : Set).prod ω) ω (λ a, (pre_exp a.fst).fun_value a.snd)
instance : has_pow Set Set := ⟨λ m n, exp.fun_value (m.pair n)⟩

lemma pre_mul_into_fun {m : Set} (hm : m ∈ ω) : m.pre_mul.into_fun ω ω := rec_fun_into_fun zero_nat (pre_add_into_fun hm)

lemma exp_eq {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) : m ^ n = (pre_exp m).fun_value n :=
begin
  let f : Set → Set := λ p, (pre_exp p.fst).fun_value p.snd,
  have hf : f (m.pair n) = (pre_exp m).fun_value n, simp only [f], rw [fst_congr, snd_congr],
  change exp.fun_value (m.pair n) = (pre_exp m).fun_value n, rw ←hf, apply pair_sep_eq_fun_value,
  have hd : exp.dom = ((ω : Set).prod ω), apply pair_sep_eq_dom_eq, intros a ha, apply rec_fun_ran,
    apply fun_value_def'',
    { exact rec_fun_is_fun one_nat, },
    { rw [pre_exp, rec_fun_dom_eq_nat],
      { exact (fst_snd_mem_dom_ran ha).right, },
      { exact one_nat, },
      { apply pre_mul_into_fun (fst_snd_mem_dom_ran ha).left, }, },
  rw [←exp, hd, pair_mem_prod], exact ⟨hm, hn⟩,
end

theorem exp_base {m : Set} (hm : m ∈ (ω : Set.{u})) : m ^ (∅ : Set.{u}) = one :=
begin
  rw [exp_eq hm zero_nat, pre_exp], refine (recursion_thm one_nat (pre_mul_into_fun hm)).left,
end

theorem exp_ind {m : Set.{u}} (hm : m ∈ (ω : Set.{u})) {n : Set.{u}} (hn : n ∈ (ω : Set.{u})) : m ^ n.succ = m ^ n * m :=
begin
  rw [exp_eq hm (nat_induct.succ_closed hn), exp_eq hm hn],
  rw [pre_exp, (recursion_thm one_nat (pre_mul_into_fun hm)).right _ hn],
  have h : ((ω : Set).rec_fun one m.pre_mul).fun_value n ∈ (ω : Set.{u}),
    apply rec_fun_ran, apply fun_value_def'' (rec_fun_is_fun one_nat),
    rw rec_fun_dom_eq_nat one_nat (pre_mul_into_fun hm), exact hn,
  rw mul_comm h hm,
  rw mul_eq hm h,
end

theorem exp_into_nat {m : Set.{u}} (hm : m ∈ (ω : Set.{u})) {n : Set.{u}} (hn : n ∈ (ω : Set.{u})) : m ^ n ∈ (ω : Set.{u}) :=
begin
  revert n, apply induction,
  { rw [exp_base hm], exact one_nat, },
  { intros n hn hi, rw [exp_ind hm hn], exact mul_into_nat hi hm, },
end

theorem exp_add {m : Set.{u}} (hm : m ∈ (ω : Set.{u})) {n : Set.{u}} (hn : n ∈ (ω : Set.{u})) {p : Set} (hp : p ∈ ω) : m ^ (n + p) = m ^ n * m ^ p :=
begin
  revert p, apply induction,
  { rw [add_base hn, exp_base hm, mul_one (exp_into_nat hm hn)], },
  { intros p hp hi, rw [add_ind hn hp, exp_ind hm (add_into_nat hn hp), hi, exp_ind hm hp],
    rw mul_assoc (exp_into_nat hm hn) (exp_into_nat hm hp) hm, },
end

theorem one_exp {m : Set.{u}} (hm : m ∈ (ω : Set.{u})) : one.{u} ^ m = one :=
begin
  revert m, apply induction,
  { rw [exp_base one_nat], },
  { intros m hm hi, rw [exp_ind one_nat hm, hi, mul_one one_nat], },
end

theorem exp_exp {m : Set.{u}} (hm : m ∈ (ω : Set.{u})) {n : Set.{u}} (hn : n ∈ (ω : Set.{u})) {p : Set} (hp : p ∈ ω) : (m ^ n) ^ p = m ^ (n * p) :=
begin
  revert p, apply induction,
  { rw [mul_base hn, exp_base hm, exp_base (exp_into_nat hm hn)], },
  { intros p hp hi, rw [exp_ind (exp_into_nat hm hn) hp, hi, mul_ind hn hp, exp_add hm (mul_into_nat hn hp) hn], },
end

theorem exp_mul {m : Set.{u}} (hm : m ∈ (ω : Set.{u})) {n : Set.{u}} (hn : n ∈ (ω : Set.{u})) {p : Set.{u}} (hp : p ∈ (ω : Set.{u})) : (m * n) ^ p = m ^ p * n ^ p :=
begin
  revert p, apply induction,
  { rw [exp_base (mul_into_nat hm hn), exp_base hm, exp_base hn, mul_one one_nat], },
  { intros p hp hi, rw [exp_ind (mul_into_nat hm hn) hp, hi, mul_assoc (mul_into_nat (exp_into_nat hm hp) (exp_into_nat hn hp)) hm hn],
    rw [←mul_assoc (exp_into_nat hm hp) (exp_into_nat hn hp) hm, mul_comm (exp_into_nat hn hp) hm],
    rw [mul_assoc (exp_into_nat hm hp) hm (exp_into_nat hn hp), exp_ind hn hp],
    rw [mul_assoc (exp_into_nat hm (nat_induct.succ_closed hp)) (exp_into_nat hn hp) hn, exp_ind hm hp], },
end

instance : has_lt Set := ⟨Set.has_mem.mem⟩
instance : has_le Set := ⟨(λ m n, m ∈ n ∨ m = n)⟩

lemma le_self {x : Set} : x ≤ x := or.inr rfl

@[simp]
lemma lt_def {n m : Set} : n < m ↔ n ∈ m := by refl

@[simp]
lemma le_iff {n m : Set} : m ≤ n ↔ m ∈ n ∨ m = n := by simp only [has_le.le]

lemma mem_succ_iff_mem {p k : Set} : p ∈ k.succ ↔ p ≤ k :=
by simp only [succ, mem_union, mem_singleton, le_iff, or_comm]

lemma mem_nat_iff {n : Set} (hn : n ∈ ω) {x : Set} : x ∈ n ↔ x ∈ ω ∧ x ∈ n :=
begin
  symmetry, simp only [and_iff_right_iff_imp],
  intro hx, apply nat_transitive_set, simp only [mem_Union, exists_prop], exact ⟨_, hn, hx⟩,
end

lemma mem_nat_of_mem_nat_of_mem {n : Set} (hn : n ∈ ω) {m : Set} (hm : m ∈ n) : m ∈ ω := ((mem_nat_iff hn).mp hm).left

lemma subset_nat_of_mem_nat {n : Set} (hn : n ∈ ω) : n ⊆ ω := (λ m hm, mem_nat_of_mem_nat_of_mem hn hm)

lemma self_mem_succ {n : Set} : n ∈ n.succ := by { rw [mem_succ_iff_mem, le_iff], finish, }
lemma self_sub_succ {n : Set} : n ⊆ n.succ :=
(λ m hmn, by { rw [mem_succ_iff_mem, le_iff], finish, })

-- Lemma 4L part a
lemma mem_iff_succ_mem_succ {m n : Set} (hm : m ∈ ω) (hn : n ∈ ω) : m ∈ n ↔ m.succ ∈ n.succ :=
begin
  split,
  { revert hm m, refine induction _ _ hn,
    { intros m hm hc, exfalso, exact mem_empty _ hc, },
    { intros k hk hi m hm hmk, rw [mem_succ_iff_mem, le_iff] at hmk, cases hmk,
      { apply self_sub_succ, exact hi hm hmk, },
      { subst hmk, exact self_mem_succ, }, }, },
  { intro he, rw [mem_succ_iff_mem, le_iff] at he, cases he,
    { apply nat_transitive hn, simp only [mem_Union, exists_prop],
      refine ⟨_, he, _⟩, exact self_mem_succ, },
    { subst he, exact self_mem_succ }, },
end

lemma mem_iff_succ_le {n : Set} (hn : n ∈ ω) {m : Set} (hm : m ∈ ω) : n ∈ m ↔ n.succ ≤ m :=
begin
  rw [mem_iff_succ_mem_succ hn hm, mem_succ_iff_mem],
end

-- Lemma 4L part b
lemma nat_not_mem_self : ∀ {n : Set}, n ∈ ω → n ∉ n :=
@induction (λ n, n ∉ n) (mem_empty _) (λ n hn hnn hsn, hnn ((mem_iff_succ_mem_succ hn hn).mpr hsn))

def nat_order : Set := Set.pair_sep Set.has_mem.mem ω ω

-- The Trichotomy Law for ω can be deduced from here
theorem nat_order_lin : (ω : Set).lin_order nat_order :=
begin
  split,
  { exact pair_sep_sub_prod, },
  { intros m n p hmn hnp, rw [nat_order, pair_mem_pair_sep] at *,
    rcases hmn with ⟨hm, hn, hmn⟩, rcases hnp with ⟨-, hp, hnp⟩, refine ⟨hm, hp, _⟩,
    apply nat_transitive hp, simp only [mem_Union, exists_prop], exact ⟨_, hnp, hmn⟩, },
  { intro m, rw [nat_order, pair_mem_pair_sep], rintro ⟨hm, -, h⟩,
    exact nat_not_mem_self hm h, },
  { suffices h : ∀ {n : Set}, n ∈ ω → ∀ {m : Set}, m ∈ ω → n = m ∨ m ∈ n ∨ n ∈ m,
      intros n m hn hm hne, specialize h hn hm, rcases h with (h|h|h),
      { contradiction, },
      { right, rw [nat_order, pair_mem_pair_sep], finish, },
      { left, rw [nat_order, pair_mem_pair_sep], finish, },
    refine @induction (λ n, ∀ {m : Set}, m ∈ ω → n = m ∨ m ∈ n ∨ n ∈ m) _ _,
    { suffices h : ∀ {m : Set}, m ∈ ω → ∅ ≤ m, simp only [le_iff] at h,
        intros m hm, cases h hm,
        { finish, },
        { finish, },
      apply induction,
      { rw [le_iff], finish, },
      { simp only [le_iff, mem_succ_iff_mem], intros m hm h, left, assumption, }, },
    { intros k hk hi m hm, specialize hi hm, rcases hi with (hi|hi|hi),
      { subst hi, right, left, exact self_mem_succ, },
      { rw [mem_succ_iff_mem, le_iff], finish, },
      { have h : k.succ ∈ m.succ, from (mem_iff_succ_mem_succ hk hm).mp hi,
        rw [mem_succ_iff_mem, le_iff] at h, finish, }, }, },
end

lemma lt_trans {k m n : Set} (hk : k ∈ ω) (hm : m ∈ ω) (hn : n ∈ ω) (hkm : k ∈ m) (hmn : m ∈ n) : k ∈ n :=
begin
  have ht : nat_order.transitive, from nat_order_lin.trans,
  specialize @ht k m n,
  simp only [nat_order, pair_mem_pair_sep] at ht,
  exact (ht ⟨hk, hm, hkm⟩ ⟨hm, hn, hmn⟩).right.right,
end

lemma not_lt_and_gt {m n : Set} (hm : m ∈ ω) (hn : n ∈ ω) : ¬ (m ∈ n ∧ n ∈ m) :=
begin
  intro h, apply nat_not_mem_self hm, exact lt_trans hm hn hm h.left h.right,
end

lemma nat_order_conn {m n : Set} (hm : m ∈ ω) (hn : n ∈ ω) (hne : m ≠ n) : m ∈ n ∨ n ∈ m :=
begin
  have h := nat_order_lin.conn hm hn hne,
  simp only [nat_order, pair_mem_pair_sep] at h, cases h,
    exact or.inl h.right.right,
  exact or.inr h.right.right,
end

instance : has_ssubset Set := ⟨(λ m n, m ⊆ n ∧ m ≠ n)⟩

lemma ssub_of_sub_of_ssub {x y z : Set} (hxy : x ⊆ y) (hyz : y ⊂ z) : x ⊂ z :=
begin
  split,
    exact subset_trans hxy hyz.left,
  intro hxz, rw ←hxz at hyz, apply hyz.right, rw eq_iff_subset_and_subset, exact ⟨hyz.left, hxy⟩,
end

@[simp]
lemma ssubset_iff {A B : Set} : A ⊂ B ↔ A ⊆ B ∧ A ≠ B := iff.rfl

-- Corollary 4M part 1
theorem nat_ssub_iff_mem {m n : Set} (hm : m ∈ ω) (hn : n ∈ ω) : m ⊂ n ↔ m ∈ n :=
begin
  split,
  { rintro ⟨hs, hne⟩, cases nat_order_lin.conn hm hn hne,
    { rw [nat_order, pair_mem_pair_sep] at h, finish, },
    { rw [nat_order, pair_mem_pair_sep] at h, rcases h with ⟨-, -, h⟩, exfalso,
      apply nat_not_mem_self hn, exact hs h, }, },
  { intro h, refine ⟨_, _⟩,
    { intros k hk, apply nat_transitive hn, simp only [mem_Union, exists_prop], exact ⟨_, h, hk⟩, },
    { intro he, subst he, exact nat_not_mem_self hm h, }, },
end

-- Corollary 4M part 2
theorem nat_sub_iff_le {m n : Set} (hm : m ∈ ω) (hn : n ∈ ω) : m ⊆ n ↔ m ≤ n :=
begin
  rw [le_iff], split,
  { intro hmn, by_cases m = n,
    { finish, },
    { left, rw ←nat_ssub_iff_mem hm hn, exact ⟨hmn, h⟩, }, },
  { rintro (h|h),
    { exact ((nat_ssub_iff_mem hm hn).mpr h).left, },
    { subst h, exact subset_self, }, },
end

-- Theorem 4N part a
theorem add_lt_add_of_lt {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) {p : Set} (hp : p ∈ ω) :
m ∈ n ↔ m + p ∈ n + p :=
begin
  revert m hm n hn p hp,
  have hleft : ∀ {m : Set}, m ∈ ω → ∀ {n : Set}, n ∈ ω → m ∈ n → ∀ {p : Set}, p ∈ ω → m + p ∈ n + p,
    intros m hm n hn hmn, apply induction,
      rw [add_base hm, add_base hn], exact hmn,
    intros k hk hi, rw [add_ind hm hk, add_ind hn hk, ←mem_iff_succ_mem_succ (add_into_nat hm hk) (add_into_nat hn hk)],
    exact hi,
  intros m hm n hn p hp,
  refine ⟨λ hmn, hleft hm hn hmn hp, _⟩,
  intro h, by_cases he : m = n,
    subst he, exfalso, exact nat_not_mem_self (add_into_nat hm hp) h,
  cases nat_order_conn hm hn he with hmn hnm,
    exact hmn,
  have h : n + p ∈ n + p,
    exact lt_trans (add_into_nat hn hp) (add_into_nat hm hp) (add_into_nat hn hp) (hleft hn hm hnm hp) h,
  exfalso, apply nat_not_mem_self (add_into_nat hn hp) h,
end

-- Theorem 4N part b
theorem mul_lt_mul_of_lt {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) {p : Set} (hp : p ∈ ω) (hpnz : p ≠ ∅) :
m ∈ n ↔ m * p ∈ n * p :=
begin
  revert m hm n hn p hp,
  have hleft : ∀ {m : Set}, m ∈ ω → ∀ {n : Set}, n ∈ ω → m ∈ n → ∀ {p : Set}, p ∈ ω → m * p.succ ∈ n * p.succ,
    intros m hm n hn hmn, apply induction,
      rw [←one, mul_one hm, mul_one hn], exact hmn,
    intros k hk hi, rw [mul_ind hm (nat_induct.succ_closed hk), mul_ind hn (nat_induct.succ_closed hk)],
    apply lt_trans (add_into_nat (mul_into_nat hm (nat_induct.succ_closed hk)) hm) (add_into_nat (mul_into_nat hn (nat_induct.succ_closed hk)) hm) (add_into_nat (mul_into_nat hn (nat_induct.succ_closed hk)) hn),
      rw ←add_lt_add_of_lt (mul_into_nat hm (nat_induct.succ_closed hk)) (mul_into_nat hn (nat_induct.succ_closed hk)) hm,
      exact hi,
    rw [add_comm (mul_into_nat hn (nat_induct.succ_closed hk)) hm, add_comm (mul_into_nat hn (nat_induct.succ_closed hk)) hn],
    rw ←add_lt_add_of_lt hm hn (mul_into_nat hn (nat_induct.succ_closed hk)),
    exact hmn,
  intros m hm n hn p hp hpnz,
  obtain ⟨q, hq, he⟩ := exists_pred_of_ne_zero hp hpnz,
  subst he, refine ⟨λ hmn, hleft hm hn hmn hq, _⟩,
  intro h, by_cases he : m = n,
    subst he, exfalso, exact nat_not_mem_self (mul_into_nat hm hp) h,
  cases nat_order_conn hm hn he with hmn hnm,
    exact hmn,
  have h : n * q.succ ∈ n * q.succ,
    exact lt_trans (mul_into_nat hn hp) (mul_into_nat hm hp) (mul_into_nat hn hp) (hleft hn hm hnm hq) h,
  exfalso, apply nat_not_mem_self (mul_into_nat hn hp) h,
end


theorem mul_lt_mul_of_lt_left {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) {p : Set} (hp : p ∈ ω) (hpnz : p ≠ ∅) :
m ∈ n ↔ p * m ∈ p * n :=
begin
  rw [mul_comm hp hm, mul_comm hp hn], exact mul_lt_mul_of_lt hm hn hp hpnz,
end

-- Corollary 4P part a
theorem cancel_add_right {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) {p : Set} (hp : p ∈ ω) (h : m + p = n + p) : m = n :=
begin
  apply classical.by_contradiction, intro hmne, cases nat_order_conn hm hn hmne with hmn hnm,
    rw [add_lt_add_of_lt hm hn hp, h] at hmn, exact nat_not_mem_self (add_into_nat hn hp) hmn,
  rw [add_lt_add_of_lt hn hm hp, h] at hnm, exact nat_not_mem_self (add_into_nat hn hp) hnm,
end

theorem cancel_add_left {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) {p : Set} (hp : p ∈ ω) (h : p + m = p + n) : m = n :=
begin
  rw [add_comm hp hm, add_comm hp hn] at h, exact cancel_add_right hm hn hp h,
end

-- Corollary 4P part b
theorem cancel_mul_right {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) {p : Set} (hp : p ∈ ω) (hpnz : p ≠ ∅) (h : m * p = n * p) : m = n :=
begin
  apply classical.by_contradiction, intro hmne, cases nat_order_conn hm hn hmne with hmn hnm,
    rw [mul_lt_mul_of_lt hm hn hp hpnz, h] at hmn, exact nat_not_mem_self (mul_into_nat hn hp) hmn,
  rw [mul_lt_mul_of_lt hn hm hp hpnz, h] at hnm, exact nat_not_mem_self (mul_into_nat hn hp) hnm,
end

theorem cancel_mul_left {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) {p : Set} (hp : p ∈ ω) (hpnz : p ≠ ∅) (h : p * m = p * n) : m = n :=
begin
  rw [mul_comm hp hm, mul_comm hp hn] at h, exact cancel_mul_right hm hn hp hpnz h,
end

lemma nonzero_exp_positive {b : Set.{u}} (hb : b ∈ nat.{u}) (hbnz : b ≠ ∅) {n : Set.{u}} (hn : n ∈ nat.{u}) : ∅ ∈ b ^ n :=
begin
  revert n, apply induction,
    rw [exp_base hb, one], exact self_mem_succ,
  intros n hn hi, rw [exp_ind hb hn, ←zero_mul hb, ←mul_lt_mul_of_lt zero_nat (exp_into_nat hb hn) hb hbnz],
  exact hi,
end

theorem nat_well_order {A : Set} (hA : A ⊆ ω) (hne : A ≠ ∅) : ∃ m : Set, m ∈ A ∧ ∀ {n : Set}, n ∈ A → m ≤ n :=
begin
  apply classical.by_contradiction, intro hc,
  have h : ∀ {m : Set}, m.mem ω → ∀ {n : Set}, n.mem m → n ∉ A,
    refine @induction (λ m, ∀ {n : Set}, n.mem m → n ∉ A) _ _,
    { intros n hn, exfalso, exact mem_empty _ hn, },
    { intros k hk hi n hnk, change n ∈ k.succ at hnk, rw [mem_succ_iff_mem, le_iff] at hnk, cases hnk,
      { exact hi hnk, },
      { subst hnk, intro hnA, refine hc ⟨_, hnA, _⟩, intros m hmA, rw le_iff, by_cases n = m,
        { exact or.inr h, },
        { cases nat_order_lin.conn hk (hA hmA) h with h' h',
          { rw [nat_order, pair_mem_pair_sep] at h', finish, },
          { rw [nat_order, pair_mem_pair_sep] at h', exfalso, exact hi h'.right.right hmA, }, }, }, },
  apply hne, rw eq_empty, intros n hnA, exact h (nat_induct.succ_closed (hA hnA)) self_mem_succ hnA,
end

lemma le_of_not_lt {n : Set} (hn : n ∈ ω) {m : Set} (hm : m ∈ ω) (h : ¬ (n ∈ m)) : m ≤ n :=
begin
  by_cases hc : m = n,
    exact or.inr hc,
  cases nat_order_conn hm hn hc with hmn hmn,
    exact or.inl hmn,
  contradiction,
end

-- Corollary 4Q
theorem not_exists_mon_dec_fun : ¬ ∃ f : Set, f.into_fun ω ω
∧ ∀ {n : Set}, n ∈ ω → f.fun_value n.succ ∈ f.fun_value n :=
begin
  rintro ⟨f, hf, ha⟩,
  have hne : f.ran ≠ ∅, intro fr, rw eq_empty at fr, apply fr (f.fun_value ∅),
    apply fun_value_def'' (is_function_of_into hf), rw dom_eq_of_into hf, exact nat_induct.zero,
  rcases nat_well_order (ran_sub_of_into hf) hne with ⟨m, hmA, ha'⟩,
  rw mem_ran at hmA, rcases hmA with ⟨k, hkm⟩,
  have hd : k ∈ f.dom, rw mem_dom, exact ⟨_, hkm⟩,
  replace hkm : m = f.fun_value k, from fun_value_def (is_function_of_into hf) hkm, subst hkm,
  simp only [le_iff] at ha',
  have hd' : k.succ ∈ f.dom, rw dom_eq_of_into hf at *, exact nat_induct.succ_closed hd,
  cases ha' (fun_value_def'' (is_function_of_into hf) hd'),
  { apply nat_not_mem_self,
    { apply ran_sub_of_into hf, exact fun_value_def'' (is_function_of_into hf) hd, },
    { have ht : nat_order.transitive, from nat_order_lin.trans,
      specialize @ht (f.fun_value k) (f.fun_value k.succ) (f.fun_value k),
      simp only [nat_order, pair_mem_pair_sep] at ht,
      have hko : (f.fun_value k).mem ω,
        apply ran_sub_of_into hf, exact fun_value_def'' (is_function_of_into hf) hd,
      have hkso : (f.fun_value k.succ).mem ω,
        apply ran_sub_of_into hf, exact fun_value_def'' (is_function_of_into hf) hd',
      refine (ht ⟨hko, hkso, h⟩ ⟨hkso, hko, ha _⟩).right.right,
      rw ←dom_eq_of_into hf, assumption, }, },
  { apply nat_not_mem_self, apply ran_sub_of_into hf, apply fun_value_def'' (is_function_of_into hf), exact hd,
    have ho : k.mem ω, rw ←dom_eq_of_into hf, assumption,
    specialize ha ho, rw ←h at ha, assumption, },
end

theorem strong_induction {A : Set} (hA : A ⊆ ω)
(h : ∀ {n : Set}, n ∈ ω → (∀ {m : Set}, m ∈ n → m ∈ A) → n ∈ A) : A = ω :=
begin
  apply classical.by_contradiction, intro hne,
  have hcne : ω \ A ≠ ∅, intro hce, apply hne, refine eq_iff_subset_and_subset.mpr ⟨hA, _⟩,
    intros n hn, apply classical.by_contradiction, intro hnA, apply mem_empty n, rw ←hce,
    rw mem_diff, exact ⟨hn, hnA⟩,
  have hs : ω \ A ⊆ ω, intros n hn, rw mem_diff at hn, exact hn.left,
  rcases nat_well_order hs hcne with ⟨m, hm, ha⟩, simp only [mem_diff] at hm ha, apply hm.right,
  apply h hm.left, intros n hnm, apply classical.by_contradiction, intro hnA,
  have hno : n.mem ω, apply nat_transitive_set, simp only [mem_Union, exists_prop],
    exact ⟨_, hm.left, hnm⟩,
  specialize ha ⟨hno, hnA⟩, rw le_iff at ha, cases ha,
  { exact not_lt_and_gt hno hm.left ⟨hnm, ha⟩, },
  { apply nat_not_mem_self hno, subst ha, exact hnm, },
end

lemma zero_ne_one : ∅ ≠ one :=
begin
  intro he, apply nat_not_mem_self zero_nat, nth_rewrite 1 he, exact self_mem_succ,
end

lemma one_ne_two : one ≠ two :=
begin
  intro he, apply nat_not_mem_self one_nat, nth_rewrite 1 he, exact self_mem_succ,
end

lemma zero_ne_two : ∅ ≠ two :=
begin
  intro he, apply nat_not_mem_self zero_nat, nth_rewrite 1 he, exact self_sub_succ self_mem_succ,
end

-- chapter 4 problem 22
lemma mem_self_add_succ {m : Set} (hm : m ∈ ω) {p : Set} (hp : p ∈ ω) : m ∈ m + p.succ :=
begin
  revert p, apply induction,
    rw [add_ind hm zero_nat, add_base hm], exact self_mem_succ,
  intros p hp hi, rw [add_ind hm hp] at hi, rw [add_ind hm (nat_induct.succ_closed hp), add_ind hm hp],
  have h : (m + p).succ ∈ (m + p).succ.succ := self_mem_succ,
  exact lt_trans hm (nat_induct.succ_closed (add_into_nat hm hp)) (nat_induct.succ_closed (nat_induct.succ_closed (add_into_nat hm hp))) hi h,
end

-- chapter 4 problem 23
lemma exists_addend_of_lt {m : Set.{u}} (hm : m ∈ (ω : Set.{u})) : ∀ {n : Set.{u}}, n ∈ (ω : Set.{u}) → m ∈ n → ∃ p : Set.{u}, p ∈ (ω : Set.{u}) ∧ m + p.succ = n :=
begin
  apply @induction (λ n : Set.{u}, m ∈ n → ∃ p : Set.{u}, p ∈ (ω : Set.{u}) ∧ m + p.succ = n),
    intro hme, exfalso, exact mem_empty _ hme,
  intros n hn hi hmn, rw [mem_succ_iff_mem, le_iff] at hmn, cases hmn,
    obtain ⟨p, hp, he⟩ := hi hmn,
    refine ⟨p.succ, nat_induct.succ_closed hp, _⟩,
    rw [add_ind hm (nat_induct.succ_closed hp), he],
  refine ⟨∅, zero_nat, _⟩, rw [add_ind hm zero_nat, add_base hm, hmn],
end

lemma lt_iff {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) : m ∈ n ↔ ∃ p : Set, p ∈ ω ∧ m + p.succ = n :=
begin
  split,
    intro hmn, exact exists_addend_of_lt hm hn hmn,
  rintro ⟨p, hp, he⟩, rw ←he, exact mem_self_add_succ hm hp,
end

lemma le_iff_exists {m : Set} (hm : m ∈ ω) {n : Set} (hn : n ∈ ω) : m ≤ n ↔ ∃ p : Set, p ∈ ω ∧ m + p = n :=
begin
  split,
    intro hmn, rw le_iff at hmn, cases hmn with hmn,
      rw lt_iff hm hn at hmn,
      rcases hmn with ⟨p, hp, he⟩, exact ⟨p.succ, (nat_induct.succ_closed hp), he⟩,
    refine ⟨∅, zero_nat, _⟩, rw [hmn, add_base hn],
  rintro ⟨p, hp, he⟩, rw le_iff, by_cases h : p = ∅,
    right, rw [h, add_base hm] at he, exact he,
  left, rw lt_iff hm hn,
  obtain ⟨k, hk, he'⟩ := exists_pred_of_ne_zero hp h,
  refine ⟨k, hk, _⟩, rw [←he', he],
end

def bool : Set := {∅, one}
def neg : Set := {pair ∅ one, pair one ∅}
def mod2 : Set := bool.rec_fun ∅ neg

lemma zero_mem_bool : ∅ ∈ bool :=
by simp [bool]

lemma one_mem_bool : one ∈ bool :=
by simp [bool]

lemma neg_into_fun : neg.into_fun bool bool :=
begin
  rw fun_def_equiv, dsimp [is_func], split,
    intros z hz, rw [neg, mem_insert, mem_singleton] at hz, cases hz,
      subst hz, rw [pair_mem_prod], exact ⟨zero_mem_bool, one_mem_bool⟩,
    subst hz, rw [pair_mem_prod], exact ⟨one_mem_bool, zero_mem_bool⟩,
  intros z hz, rw [bool, mem_insert, mem_singleton] at hz, cases hz,
    subst hz, use one, simp only [neg, mem_insert, mem_singleton], refine ⟨or.inl rfl, _⟩,
    rintros b (hb|hb),
      exact (pair_inj hb).right,
    exfalso, apply zero_ne_one, exact (pair_inj hb).left,
  subst hz, use ∅, simp only [neg, mem_insert, mem_singleton], refine ⟨or.inr rfl, _⟩,
  rintros b (hb|hb),
    exfalso, apply zero_ne_one, symmetry, exact (pair_inj hb).left,
  exact (pair_inj hb).right,
end

lemma neg_fun_value_zero : neg.fun_value ∅ = one :=
begin
  symmetry, apply fun_value_def neg_into_fun.left, simp [neg],
end

lemma neg_fun_value_one : neg.fun_value one = ∅ :=
begin
  symmetry, apply fun_value_def neg_into_fun.left, simp [neg],
end

lemma self_eq_one_of_neq_eq_zero {n : Set} (hn : n ∈ bool) (h : neg.fun_value n = ∅) : n = one  :=
begin
  simp [bool] at hn, cases hn,
    subst hn, exfalso, rw neg_fun_value_zero at h, exact zero_ne_one h.symm,
  exact hn,
end

lemma self_eq_zero_of_neq_eq_one {n : Set} (hn : n ∈ bool) (h : neg.fun_value n = one) : n = ∅  :=
begin
  simp [bool] at hn, cases hn,
    exact hn,
  subst hn, exfalso, rw neg_fun_value_one at h, exact zero_ne_one h,
end

lemma mod2_zero : mod2.fun_value ∅ = ∅ :=
(recursion_thm zero_mem_bool neg_into_fun).left

lemma mod2_succ {n : Set} (hn : n ∈ ω) : mod2.fun_value n.succ = neg.fun_value (mod2.fun_value n) :=
(recursion_thm zero_mem_bool neg_into_fun).right _ hn

lemma mod2_fun_value_mem {n : Set} (hn : n ∈ ω) : mod2.fun_value n ∈ bool :=
begin
  apply rec_fun_ran, apply fun_value_def'' (rec_fun_is_fun zero_mem_bool),
  rw rec_fun_dom_eq_nat zero_mem_bool neg_into_fun, exact hn,
end

lemma mod2_fun_value_eq_zero_or_one {n : Set} (hn : n ∈ ω) : mod2.fun_value n = ∅ ∨ mod2.fun_value n = one :=
begin
  have h := mod2_fun_value_mem hn,
  rw [bool, mem_insert, mem_singleton] at h, exact h,
end

def pred : Set := succ_fun.inv ∪ {pair ∅ ∅}

lemma pred_onto_fun : pred.onto_fun (ω : Set.{u}) ω :=
begin
  have hd : succ_fun.inv.dom ∪ dom {(∅ : Set.{u}).pair ∅} = ω,
    rw [dom_singleton, T3E_a, succ_fun_ran, union_comm], apply union_diff_eq_self_of_subset,
    intros x hx, rw mem_singleton at hx, subst hx, exact zero_nat,
  have hr : succ_fun.inv.ran ∪ ran {(∅ : Set.{u}).pair ∅} = ω,
    rw [ran_single_pair, T3E_b, succ_fun_into_fun.right.left],
    apply union_eq_left_of_subset, intros x hx, rw mem_singleton at hx, subst hx, exact zero_nat,
  nth_rewrite 0 ←hd, rw ←hr, refine union_fun _ singleton_is_fun _,
    rw T3F_a, exact succ_one_to_one,
  rw [dom_singleton, T3E_a, succ_fun_ran, inter_comm], exact self_inter_diff_empty,
end

lemma pred_succ_eq_self {n : Set} (hn : n ∈ ω) : pred.fun_value n.succ = n :=
begin
  symmetry, apply fun_value_def pred_onto_fun.left,
  rw [pred, mem_union, pair_mem_inv], left, apply fun_value_def''' succ_fun_into_fun.left,
    rw succ_fun_into_fun.right.left, exact hn,
  exact succ_fun_value hn,
end

lemma pred_oto {n : Set} (hn : n ∈ ω) (hnz : n ≠ ∅) {m : Set} (hm : m ∈ ω) (hmz : m ≠ ∅)
(h : pred.fun_value n = pred.fun_value m) : n = m :=
begin
  obtain ⟨p, hp, hpe⟩ := exists_pred_of_ne_zero hn hnz,
  obtain ⟨q, hq, hqe⟩ := exists_pred_of_ne_zero hm hmz,
  subst hpe, subst hqe, rw [pred_succ_eq_self hp, pred_succ_eq_self hq] at h, rw h,
end

lemma mod2_spec : ∀ {n : Set.{u}}, n ∈ (ω : Set.{u}) → (mod2.fun_value n = ∅ → ∃ k, k ∈ (ω : Set.{u}) ∧ n = two * k) ∧ (mod2.fun_value n = one → ∃ k, k ∈ (ω : Set.{u}) ∧ n = (two * k).succ) :=
begin
  apply induction,
    split,
      intro h, refine ⟨_, zero_nat, _⟩, rw mul_base two_nat,
    intro h, exfalso, rw mod2_zero at h, exact zero_ne_one h,
  intros n hn hi,
  split,
    intro h, rw mod2_succ hn at h, rw self_eq_one_of_neq_eq_zero (mod2_fun_value_mem hn) h at hi,
    obtain ⟨k, hk, he⟩ := hi.right rfl,
    refine ⟨_, nat_induct.succ_closed hk, _⟩,
    rw [he, mul_ind two_nat hk],
    change (two * k).succ.succ = two * k + one.succ,
    rw [add_ind (mul_into_nat two_nat hk) one_nat],
    rw [one, add_ind (mul_into_nat two_nat hk) zero_nat, add_base (mul_into_nat two_nat hk)],
  intro h, rw mod2_succ hn at h, rw self_eq_zero_of_neq_eq_one (mod2_fun_value_mem hn) h at hi,
  obtain ⟨k, hk, he⟩ := hi.left rfl,
  rw he, exact ⟨_, hk, rfl⟩,
end

lemma mod2_spec_zero {n : Set} (hn : n ∈ ω) (h : mod2.fun_value n = ∅) : ∃ k, k ∈ ω ∧ n = two * k :=
(mod2_spec hn).left h

lemma mod2_spec_one {n : Set} (hn : n ∈ ω) (h : mod2.fun_value n = one) : ∃ k, k ∈ ω ∧ n = (two * k).succ :=
(mod2_spec hn).right h

-- set_option pp.universes true

lemma mod2_spec_one' {n : Set} (hn : n ∈ ω) (h : mod2.fun_value n = one) : ∃ k, k ∈ (ω : Set.{u}) ∧ n = pred.fun_value (two.{u} * succ k) :=
begin
  obtain ⟨k, hk, he⟩ := mod2_spec_one hn h,
  refine ⟨_, hk, _⟩, rw [mul_ind two_nat hk],
  have two_mul_k := mul_into_nat two_nat hk,
  change n = pred.fun_value (two * k + one.succ), rw add_ind two_mul_k one_nat,
  change n = pred.fun_value (two * k + succ ∅).succ, rw add_ind two_mul_k zero_nat,
  rw add_base two_mul_k, rw ←he, symmetry, exact pred_succ_eq_self hn,
end

def divides (n m : Set) : Prop := ∃ k : Set, k ∈ ω ∧ m = k * n
def composite (n : Set) : Prop := ∃ a : Set, a < n ∧ ∃ b : Set, b < n ∧ n = a * b  
def prime (n : Set) : Prop := ¬ n.composite

lemma two_pow_lemma {n : Set.{u}} (hn : n ∈ nat.{u}) {m : Set} (hm : m ∈ ω) : two * (two.{u} ^ n * m) = two ^ n.succ * m :=
begin
  have two_exp_n := exp_into_nat two_nat hn,
  rw [exp_ind two_nat hn, mul_assoc two_nat two_exp_n hm, mul_comm two_nat two_exp_n],
end

lemma pre_nonzero_nat_factor_two : ∀ {n : Set.{u}}, n ∈ (ω : Set.{u}) → ∀ {m : Set}, m < n → m ≠ ∅ → ∃ l : Set.{u}, l ∈ (ω : Set.{u}) ∧ ∃ k : Set, k ∈ (ω : Set.{u}) ∧ mod2.fun_value k = one ∧ m = two.{u} ^ l * k :=
begin
  refine @induction _ _ _,
    intros m hm, exfalso, exact mem_empty _ hm,
  intros n hn hi m hmn hmnz,
  have hm : m ∈ (ω : Set.{u}) := mem_nat_of_mem_nat_of_mem (nat_induct.succ_closed hn) hmn,
  have hfe := mod2_fun_value_eq_zero_or_one hm,
  cases hfe,
    obtain ⟨k, hk, he⟩ := mod2_spec_zero hm hfe,
    have hknz : k ≠ ∅, intro hkz, subst hkz, subst he, apply hmnz, rw mul_base two_nat,
    have hsk : k < two * k, nth_rewrite 0 ←one_mul hk,
      rw [lt_def, ←mul_lt_mul_of_lt one_nat two_nat hk hknz], dsimp [two],
      exact self_mem_succ,
    have hkn : k < n, simp only [lt_def] at *, subst he, rw [mem_succ_iff_mem, le_iff] at hmn, cases hmn,
        exact lt_trans hk (mul_into_nat two_nat hk) hn hsk hmn,
      rw ←hmn, exact hsk,
    obtain ⟨p, hp, q, hq, hqo, he'⟩ := hi hkn hknz,
    refine ⟨p.succ, nat_induct.succ_closed hp, _, hq, hqo, _⟩,
    rw [he', two_pow_lemma hp hq] at he, exact he,
  refine ⟨_, zero_nat, _, hm, hfe, _⟩,
  rw [exp_base two_nat, one_mul hm],
end

lemma nonzero_nat_factor_two {n : Set} (hn : n ∈ ω) (hnz : n ≠ ∅) :
∃ l : Set.{u}, l ∈ (ω : Set.{u}) ∧ ∃ k : Set, k ∈ (ω : Set.{u}) ∧ mod2.fun_value k = one ∧ n = two.{u} ^ l * k :=
begin
  refine pre_nonzero_nat_factor_two (nat_induct.succ_closed hn) _ hnz,
  rw [lt_def], exact self_mem_succ,
end

lemma mod2_of_sum_mod2_of_mod2 {a : Set.{u}} (ha : a ∈ nat.{u}) {b : Set.{u}} (hb : b ∈ nat.{u})
(habe : two.divides (a + b)) (hae : two.divides a) : two.divides b :=
begin
  obtain ⟨n, hn, hne⟩ := habe,
  obtain ⟨m, hm, hme⟩ := hae,
  have haab : a ≤ a + b, rw [add_comm ha hb], nth_rewrite 0 ←zero_add ha, rw le_iff, by_cases hbe : b = ∅,
      right, rw hbe,
    left, cases nat_order_conn hb zero_nat hbe,
      rw ←add_lt_add_of_lt zero_nat hb ha, exfalso, exact mem_empty _ h,
    rw ←add_lt_add_of_lt zero_nat hb ha, exact h,
  rw [hne, hme] at haab, rw le_iff at haab, cases haab,
    rw [←mul_lt_mul_of_lt hm hn two_nat zero_ne_two.symm, lt_iff hm hn] at haab,
    rcases haab with ⟨q, hq, hqe⟩, rw [hme, ←hqe, mul_comm (add_into_nat hm (nat_induct.succ_closed hq)) two_nat, mul_add two_nat hm (nat_induct.succ_closed hq), mul_comm hm two_nat] at hne,
    have two_mul_m := mul_into_nat two_nat hm,
    have two_mul_q := mul_into_nat two_nat (nat_induct.succ_closed hq),
    refine ⟨_, nat_induct.succ_closed hq, _⟩,
    rw [mul_comm (nat_induct.succ_closed hq) two_nat, cancel_add_left hb two_mul_q two_mul_m], rw hne,
  have n_mul_two := mul_into_nat hn two_nat,
  rw [hme, haab] at hne, nth_rewrite 1 ←add_base n_mul_two at hne,
  refine ⟨∅, zero_nat, _⟩, rw zero_mul two_nat,
  apply cancel_add_left hb zero_nat n_mul_two hne,
end

lemma not_two_divides_one : ¬ two.divides one :=
begin
  rintro ⟨k, hk, he⟩, by_cases h : k = ∅,
    rw [h, zero_mul two_nat] at he, exact zero_ne_one.symm he,
  obtain ⟨m, hm, hme⟩ := exists_pred_of_ne_zero hk h, subst hme,
  have hom : one ≤ m.succ,
    rw le_iff, by_cases hmz : m = ∅,
      right, rw [hmz, one],
    left, rw [one, ←mem_iff_succ_mem_succ zero_nat hm],
    rcases nat_order_conn hm zero_nat hmz with (hmp|hmn),
      exfalso, exact mem_empty _ hmp,
    exact hmn,
  rw le_iff at hom, cases hom,
    rw [he] at hom, nth_rewrite 1 ←mul_one hk at hom,
    rw ←mul_lt_mul_of_lt_left two_nat one_nat hk h at hom,
    apply nat_not_mem_self two_nat, apply lt_trans two_nat one_nat two_nat hom,
    rw two, exact self_mem_succ,
  rw [hom] at he, nth_rewrite 0 ←mul_one hk at he, apply one_ne_two,
  apply cancel_mul_left one_nat two_nat hk h he,
end

end Set