import ch4
universe u
namespace Set

local attribute [irreducible] mem

reserve infix ` ≈ `:50
reserve infix ` ≉ `:50
reserve infix ` ≼ `:50

structure correspondence (A B f : Set) : Prop :=
(onto : f.onto_fun A B)
(oto : f.one_to_one)

def equinumerous (A B : Set) : Prop := ∃ f : Set, A.correspondence B f
infix ≈ := equinumerous
infix ≉ := (λ A B : Set, ¬(A ≈ B))

def nat_prod_nat_equin_nat : prod nat.{u} nat.{u} ≈ nat.{u} :=
begin
  let f : Set := pair_sep_eq (prod ω ω) ω (λ z, pred.fun_value (two ^ z.fst * (two * z.snd).succ)),
  refine ⟨f, ⟨pair_sep_eq_is_fun, pair_sep_eq_dom_eq _, pair_sep_eq_ran_eq _⟩, pair_sep_eq_oto _⟩,
  { intros z hz, rw mem_prod at hz, rcases hz with ⟨m, hm, n, hn, he⟩, subst he, simp only [fst_congr, snd_congr],
    rw ←pred_onto_fun.right.right, apply fun_value_def'' pred_onto_fun.left, rw pred_onto_fun.right.left,
    exact mul_into_nat (exp_into_nat two_nat hm) (nat_induct.succ_closed (mul_into_nat two_nat hn)), },
  { intros k hk,
    have hmod2 := mod2_fun_value_mem hk,
    simp [bool] at hmod2, cases hmod2,
      obtain ⟨n, hn, he⟩ := mod2_spec_zero hk hmod2, subst he,
      use pair ∅ n, split,
        rw pair_mem_prod, exact ⟨zero_nat, hn⟩,
      dsimp, rw [fst_congr, snd_congr, exp_base two_nat, one_mul (nat_induct.succ_closed hk), pred_succ_eq_self hk],
    obtain ⟨q, hq, he⟩ := mod2_spec_one' hk hmod2,
    obtain ⟨n, hn, l, hl, hlo, he'⟩ := nonzero_nat_factor_two (nat_induct.succ_closed hq) succ_neq_empty,
    obtain ⟨m, hm, he''⟩ := mod2_spec_one hl hlo,
    rw [he', two_pow_lemma hn hl, he''] at he, subst he, use n.succ.pair m, dsimp,
    rw [pair_mem_prod, fst_congr, snd_congr],
    exact ⟨⟨nat_induct.succ_closed hn, hm⟩, rfl⟩, },
  {
    have hnez : ∀ {n : Set.{u}}, n ∈ nat.{u} → ∀ {m : Set}, m ∈ nat.{u} → two.{u} ^ n * (two * m).succ ≠ ∅,
      intros n hn m hm he, apply mem_empty ∅, nth_rewrite 1 ←he,
      rw ←zero_mul (nat_induct.succ_closed (mul_into_nat two_nat hm)),
      rw ←mul_lt_mul_of_lt zero_nat (exp_into_nat two_nat hn) (nat_induct.succ_closed (mul_into_nat two_nat hm)) succ_neq_empty,
      exact nonzero_exp_positive two_nat zero_ne_two.symm hn,
    have hnmnat : ∀ {n : Set.{u}}, n ∈ nat.{u} → ∀ {m : Set}, m ∈ nat.{u} → two.{u} ^ n * (two * m).succ ∈ nat.{u},
      intros n hn m hm,
      exact mul_into_nat (exp_into_nat two_nat hn) (nat_induct.succ_closed (mul_into_nat two_nat hm)),
    have hcases : ∀ {n : Set.{u}}, n ∈ nat.{u} → ∀ {m : Set}, m ∈ nat.{u} →
      ∀ {n' : Set.{u}}, n' ∈ nat.{u} → ∀ {m' : Set}, m' ∈ nat.{u} → two ^ n * (two * m).succ = two.{u} ^ n' * (two * m').succ → n ∈ n' → false,
      intros n hn m hm n' hn' m' hm' he hnn',
      rw lt_iff hn hn' at hnn', rcases hnn' with ⟨k, hk, hke⟩, rw ←hke at he,
      rw exp_add two_nat hn (nat_induct.succ_closed hk) at he,
      have two_exp_n := exp_into_nat two_nat hn,
      have two_mul_m' := nat_induct.succ_closed (mul_into_nat two_nat hm'),
      rw ←mul_assoc two_exp_n (exp_into_nat two_nat (nat_induct.succ_closed hk)) two_mul_m' at he,
      have two_exp_n_nz : (two.{u} ^ n) ≠ ∅, intro h, apply mem_empty ∅, nth_rewrite 1 ←h,
        refine nonzero_exp_positive two_nat zero_ne_two.symm hn,
      replace he := cancel_mul_left (nat_induct.succ_closed (mul_into_nat two_nat hm)) (hnmnat (nat_induct.succ_closed hk) hm') two_exp_n two_exp_n_nz he,
      rw exp_ind two_nat hk at he,
      have two_exp_k := exp_into_nat two_nat hk,
      rw [mul_comm two_exp_k two_nat, ←mul_assoc two_nat two_exp_k two_mul_m', mul_comm two_nat (mul_into_nat two_exp_k two_mul_m')] at he,
      have two_mul_m := mul_into_nat two_nat hm,
      rw succ_eq_add_one two_mul_m at he,
      have tdo : two.divides one, apply mod2_of_sum_mod2_of_mod2 two_mul_m one_nat,
          rw he, refine ⟨_, mul_into_nat two_exp_k two_mul_m', rfl⟩,
        refine ⟨_, hm, _⟩, rw mul_comm two_nat hm,
      exact not_two_divides_one tdo,
    simp only [mem_prod], rintros z ⟨n, hn, m, hm, hz⟩ z' ⟨n', hn', m', hm', hz'⟩ he, subst hz, subst hz',
    simp only [fst_congr, snd_congr] at he,
    replace he := pred_oto (hnmnat hn hm) (hnez hn hm) (hnmnat hn' hm') (hnez hn' hm') he,
    have hnn' : n = n', apply classical.by_contradiction, intro hnn',
      replace hnn' := nat_order_conn hn hn' hnn', cases hnn',
        exact hcases hn hm hn' hm' he hnn',
      exact hcases hn' hm' hn hm he.symm hnn',
    rw ←hnn' at he,
    have two_exp_n_nz : two.{u} ^ n ≠ ∅, intro h, apply mem_empty ∅, nth_rewrite 1 ←h,
      refine nonzero_exp_positive two_nat zero_ne_two.symm hn,
    replace he := cancel_mul_left (nat_induct.succ_closed (mul_into_nat two_nat hm)) (nat_induct.succ_closed (mul_into_nat two_nat hm')) (exp_into_nat two_nat hn) two_exp_n_nz he,
    replace he := succ_inj (mul_into_nat two_nat hm) (mul_into_nat two_nat hm') he,
    replace he := cancel_mul_left hm hm' two_nat zero_ne_two.symm he,
    congr,
      exact hnn',
    exact he, },
end

local attribute [instance] classical.prop_decidable

def char_fun (B A : Set) : Set := pair_sep (λ b c, c = if b ∈ A then one else ∅) B two

lemma char_fun_into_fun {B A : Set} : (B.char_fun A).into_fun B two :=
begin
  refine ⟨pair_sep_eq_is_fun, pair_sep_eq_dom_eq _, pair_sep_eq_ran_sub⟩,
  intros b hb, simp only [hb, if_true, two, succ, mem_union, one, mem_singleton], finish,
end

lemma char_fun_value {B A x : Set} (hx : x ∈ B) : (B.char_fun A).fun_value x = if x ∈ A then one else ∅ :=
begin
  symmetry, apply fun_value_def (is_function_of_into char_fun_into_fun),
  simp only [char_fun, pair_mem_pair_sep], refine ⟨hx, _, rfl⟩,
  by_cases h : x ∈ A,
  { simp only [h, if_true, two, succ, mem_union, mem_singleton], finish, },
  { simp only [h, if_false, two, succ, mem_union, one, mem_singleton], finish, },
end

lemma char_fun_value' {B A x : Set} (hx : x ∈ B) : (B.char_fun A).fun_value x = one ↔ x ∈ A :=
begin
  rw char_fun_value hx, by_cases h : x ∈ A,
  { simp only [h, if_true, eq_self_iff_true], },
  { simp only [h, if_false, iff_false], intro he,
    simp only [one, succ] at he, apply mem_empty ∅,
    nth_rewrite 1 he, rw [mem_union, mem_singleton], finish, },
end

def powerset_corr (B : Set) : Set := pair_sep (λ A f, f = B.char_fun A) B.powerset (B.into_funs two)

lemma powerset_corr_onto {B : Set.{u}} : B.powerset_corr.onto_fun B.powerset (B.into_funs two) :=
begin
  refine ⟨pair_sep_eq_is_fun, pair_sep_eq_dom_eq _, pair_sep_eq_ran_eq _⟩,
  { intros A hA, rw mem_into_funs, exact char_fun_into_fun, },
  { intros f hf,
    let A := {b ∈ B | f.fun_value b = one}, refine ⟨A, _, _⟩,
    { simp only [mem_powerset], intro a, rw mem_sep, finish, }, rw mem_into_funs at hf,
      apply fun_ext (is_function_of_into hf) (is_function_of_into char_fun_into_fun),
      { rw [dom_eq_of_into hf, dom_eq_of_into char_fun_into_fun], },
      { intros x hx, apply fun_value_def (is_function_of_into char_fun_into_fun),
        simp only [char_fun, pair_mem_pair_sep], refine ⟨_, _, _⟩,
        { rw ←dom_eq_of_into hf, assumption, },
        { apply ran_sub_of_into hf, exact fun_value_def'' (is_function_of_into hf) hx, },
        by_cases h : x ∈ A,
        { simp only [h, if_true], rw [mem_sep] at h, finish, },
        { simp only [h, if_false],
          have hor : (f.fun_value x) ∈ two.{u},
            apply ran_sub_of_into hf, exact fun_value_def'' (is_function_of_into hf) hx,
          rw dom_eq_of_into hf at hx,
          simp only [two, succ, mem_union, mem_singleton] at hor, conv at hor {
            find (f.fun_value x ∈ one.{u}) { rw one },
          }, simp only [succ, mem_union, mem_singleton, iff_false_intro (mem_empty (f.fun_value x)), or_false] at hor,
          rw mem_sep at h,
          cases hor,
          { exfalso, apply h, finish, },
          { finish, }, }, }, },
end

lemma powerset_corr_fun_value {B A : Set} (hB : A ⊆ B) : B.powerset_corr.fun_value A = B.char_fun A :=
begin
  symmetry, apply fun_value_def pair_sep_eq_is_fun, simp only [pair_mem_pair_sep, mem_powerset, mem_into_funs],
  exact ⟨hB, char_fun_into_fun, rfl⟩,
end

lemma powerset_corr_oto {B : Set} : B.powerset_corr.one_to_one :=
begin
  apply one_to_one_of (is_function_of_into (into_of_onto powerset_corr_onto)),
  intros A hA A' hA' hne he, apply hne,
  simp only [dom_eq_of_into (into_of_onto powerset_corr_onto), mem_powerset] at hA hA',
  rw [powerset_corr_fun_value hA, powerset_corr_fun_value hA'] at he,
  apply ext, intro x,
  split,
  { intro hx, rw ←char_fun_value' (hA hx), rw ←he, rw char_fun_value' (hA hx), assumption, },
  { intro hx, rw ←char_fun_value' (hA' hx), rw he, rw char_fun_value' (hA' hx), assumption, },
end

lemma powerset_corr_corr {A : Set} : A.powerset.correspondence (A.into_funs two) A.powerset_corr
:= ⟨powerset_corr_onto, powerset_corr_oto⟩

-- example on page 131
theorem powerset_equinumerous_into_funs {A : Set} : A.powerset.equinumerous (A.into_funs two) := ⟨_, powerset_corr_corr⟩

-- Theorem 6A part a
theorem equin_refl {A : Set} : A.equinumerous A := ⟨_, id_onto, id_oto⟩

lemma corr_symm {A B f : Set} (h : correspondence A B f) : correspondence B A f.inv :=
begin
  split,
    split,
      rw T3F_a, exact h.oto,
    rw [T3E_a, T3E_b], exact ⟨h.onto.right.right, h.onto.right.left⟩,
  rw ←T3F_b h.onto.left.left, exact h.onto.left,
end

-- Theorem 6A part b
theorem equin_symm {A B : Set} (heq : A.equinumerous B) : B.equinumerous A :=
begin
  rcases heq with ⟨F, hF⟩, exact ⟨F.inv, corr_symm hF⟩,
end

lemma corr_trans {A B C f g : Set} (hAB : correspondence A B f) (hBC : correspondence B C g) :
  correspondence A C (g.comp f) :=
begin
  have hfun : (g.comp f).is_function := T3H_a hBC.onto.left hAB.onto.left,
  have hdom : (g.comp f).dom = f.dom,
    rw T3H_b hBC.onto.left hAB.onto.left, apply ext, intro x,
    rw [mem_sep, hBC.onto.right.left, hAB.onto.right.left, and_iff_left_iff_imp, ←hAB.onto.right.left, ←hAB.onto.right.right],
    exact fun_value_def'' hAB.onto.left,
  refine ⟨⟨hfun, _, _⟩, _⟩,
  { rw hdom, exact hAB.onto.right.left, },
  { apply ext, intro z,
    simp only [mem_ran_iff hfun, ←hBC.onto.right.right, mem_ran_iff hBC.onto.left, hBC.onto.right.left, ←hAB.onto.right.right, mem_ran_iff hAB.onto.left, hdom], split,
    { rintro ⟨x, hx, he⟩, refine ⟨f.fun_value x, ⟨_, hx, rfl⟩, _⟩, rw ←T3H_c hBC.onto.left hAB.onto.left, assumption, rw hdom, assumption, },
    { rintro ⟨y, ⟨x, hx, he⟩, he'⟩, refine ⟨x, hx, _⟩, rw T3H_c hBC.onto.left hAB.onto.left, rw ←he, assumption, rw hdom, assumption, }, },
  { apply one_to_one_of hfun, intros x hx x' hx' hne he, apply hne,
    rw [T3H_c hBC.onto.left hAB.onto.left hx, T3H_c hBC.onto.left hAB.onto.left hx'] at he,
    apply from_one_to_one hAB.onto.left hAB.oto, rw ←hdom, assumption, rw ←hdom, assumption,
    apply from_one_to_one hBC.onto.left hBC.oto,
    { rw [hBC.onto.right.left, ←hAB.onto.right.right], apply fun_value_def'' hAB.onto.left, rw ←hdom, assumption, },
    { rw [hBC.onto.right.left, ←hAB.onto.right.right], apply fun_value_def'' hAB.onto.left, rw ←hdom, assumption, },
    assumption, },
end

-- Theorem 6A part c
theorem equin_trans {A B C : Set} (hAB : A.equinumerous B) (hBC : B.equinumerous C) : A.equinumerous C :=
begin
  rcases hAB with ⟨F, hF⟩, rcases hBC with ⟨G, hG⟩, exact ⟨G.comp F, corr_trans hF hG⟩,
end

-- Prove that omega.times omega is equinumerous to omega
-- Porve that the set of nats is equinumerous to the set of rational numbers
-- Prove Theorem 6A part a (omega is not equinumerous to the set of real numbers)

-- Theorem 6B part b
theorem not_equin_powerset {A : Set} : ¬ A.equinumerous A.powerset :=
begin
  rintro ⟨g, gonto, goto⟩,
  let B := { x ∈ A | x ∉ g.fun_value x },
  have hB : B ∈ g.ran,
    rw [gonto.right.right, mem_powerset], intro x, rw [mem_sep], intro h, finish,
  rw [mem_ran_iff gonto.left, gonto.right.left] at hB, rcases hB with ⟨x, hx, he⟩,
  have h : x ∈ B ↔ x ∉ g.fun_value x,
    simp only [mem_sep, hx, true_and],
  rw he at h, exact (iff_not_self _).mp h,
end

def is_finite (A : Set) : Prop := ∃ n : Set, n ∈ ω ∧ A.equinumerous n

lemma finite_of_equin_finite {A : Set} (hA : A.is_finite) {B : Set} (hAB : A ≈ B) : B.is_finite :=
begin
  rcases hA with ⟨n, hn, hAn⟩, exact ⟨_, hn, equin_trans (equin_symm hAB) hAn⟩,
end

theorem pigeonhole : ∀ {n : Set}, n ∈ ω → ∀ {A : Set}, A ⊂ n → ¬ n.equinumerous A :=
begin
  suffices h : ∀ {n : Set}, n ∈ ω → ∀ {f : Set}, f.into_fun n n → f.one_to_one → f.ran = n,
    rintros n hn A hA ⟨f, fonto, foto⟩, simp at hA,
    have h : A = n, rw ←fonto.right.right,
      have hinto : f.into_fun n n, refine ⟨fonto.left, fonto.right.left, _⟩,
        rw fonto.right.right, exact hA.left,
      exact h hn hinto foto,
    exact hA.right h,
  apply @induction (λ n, ∀ {f : Set}, f.into_fun n n → f.one_to_one → f.ran = n),
  { intros f hinto foto, simp only [←mem_into_funs, ex2, mem_singleton] at hinto, rw hinto, apply ext, intro y,
    simp only [mem_ran, iff_false_intro (mem_empty _), exists_false], },
  { intros k hk hi,
    have hcaseI : ∀ {f : Set}, f.into_fun k.succ k.succ → f.one_to_one → (∀ {n : Set}, n ∈ k → f.fun_value n ∈ k) → f.ran = k.succ,
      intros f hinto hoto hc,
      have hf : {k.pair (f.fun_value k)} ∪ f.restrict k = f,
        have hd : k ∈ f.dom, rw hinto.right.left, exact self_mem_succ,
        rw ←restrict_singleton_eq hinto.left hd, apply restrict_combine hinto.left.left,
        rw [hinto.right.left, succ],
      have hd : k ⊆ f.dom, rw [hinto.right.left], exact self_sub_succ,
      have hf' : (f.restrict k).ran = k,
        have hr : (f.restrict k).ran ⊆ k,
          intro n, rw [mem_ran_iff (restrict_is_function hinto.left), restrict_dom hd],
          rintro ⟨x, hx, he⟩, rw he, rw restrict_fun_value hinto.left hd hx, exact hc hx,
        rw eq_iff_subset_and_subset, refine ⟨hr, _⟩,
        have frinto : (f.restrict k).into_fun k k, refine ⟨restrict_is_function hinto.left, restrict_dom hd, hr⟩,
        have froto: (f.restrict k).one_to_one := restrict_one_to_one hinto.left hoto hd,
        rw hi frinto froto, exact subset_self,
      have hf'' : ({k.pair (f.fun_value k)} : Set).ran = {k}, rw ran_singleton, rw singleton_eq,
        have ho : f.fun_value k ∈ k ∨ f.fun_value k = k, rw [←le_iff, ←mem_succ_iff_mem],
          apply hinto.right.right, apply fun_value_def'' hinto.left, rw hinto.right.left, exact self_mem_succ,
        cases ho,
        { exfalso, nth_rewrite 1 ←hf' at ho, rw [mem_ran_iff, restrict_dom hd] at ho,
          rcases ho with ⟨n, hn, he⟩, rw restrict_fun_value hinto.left hd hn at he,
          have h : k = n, apply from_one_to_one hinto.left hoto,
            { rw hinto.right.left, exact self_mem_succ, },
            { rw hinto.right.left, exact lt_trans ((mem_nat_iff hk).mp hn).left hk (nat_induct.succ_closed hk) hn self_mem_succ, },
            { exact he, },
          rw ←h at hn, exact nat_not_mem_self hk hn,
          exact restrict_is_function hinto.left, },
        { assumption, },
      rw [←hf, ran_union, hf', hf'', succ],
    intros f hinto hoto, by_cases hc : ∃ n : Set, n ∈ k ∧ f.fun_value n = k,
    { rcases hc with ⟨p, hp, he⟩,
      let f' : Set := {p.pair (f.fun_value k), k.pair k} ∪ (f \ {p.pair k, k.pair (f.fun_value k)}),
      have hps : p ∈ k.succ := self_sub_succ hp,
      have hr : ∀ {x : Set}, x ∈ k.succ → f.fun_value x ∈ k.succ, intros x hx,
        apply hinto.right.right, rw ←hinto.right.left at hx, exact fun_value_def'' hinto.left hx,
      have f'into : f'.into_fun k.succ k.succ, rw fun_def_equiv, refine ⟨λ z hz, _, λ x hx, _⟩,
        { simp only [mem_union, mem_insert, mem_singleton, mem_diff] at hz,
          simp only [mem_prod], rcases hz with (hz|hz)|⟨hm,hz⟩,
          { exact ⟨_, hps, _, hr self_mem_succ, hz⟩, },
          { exact ⟨_, self_mem_succ, _, self_mem_succ, hz⟩, },
          { rw fun_def_equiv at hinto, replace hinto := hinto.left hm, rw mem_prod at hinto, assumption, }, },
        { rw fun_def_equiv at hinto, simp only [mem_union, mem_insert, mem_singleton, mem_diff],
          by_cases hep : x = p,
          { rw hep, refine ⟨_, or.inl (or.inl rfl), _⟩, rintros y ((hz|hz)|⟨hm,hz⟩),
            { exact (pair_inj hz).right, },
            { rw [←(pair_inj hz).left, (pair_inj hz).right, he], },
            { rw ←fun_def_equiv at hinto, exfalso, apply hz, left, rw ←he,
              rw fun_value_def hinto.left hm, }, },
          { rw [mem_succ_iff_mem, le_iff] at hx, cases hx,
            { rw ←fun_def_equiv at hinto, refine ⟨f.fun_value x, or.inr ⟨fun_value_def' hinto.left _, _⟩, _⟩,
              { rw hinto.right.left, exact self_sub_succ hx, },
              { rintro (hpe|hpe),
                { exact hep (pair_inj hpe).left, },
                { rw (pair_inj hpe).left at hx, exact nat_not_mem_self hk hx, }, },
              { rintros y ((hz|hz)|⟨hm,hz⟩),
                { exfalso, exact hep (pair_inj hz).left, },
                { exfalso, rw (pair_inj hz).left at hx, exact nat_not_mem_self hk hx, },
                { exact fun_value_def hinto.left hm, }, }, },
            { rw hx, refine ⟨_, or.inl (or.inr rfl), _⟩, rintros y ((hz|hz)|⟨hm,hz⟩),
              { exfalso, rw (pair_inj hz).left at hx, exact hep hx, },
              { exact (pair_inj hz).right, },
              { exfalso, apply hz, right, rw ←fun_def_equiv at hinto, rw fun_value_def hinto.left hm, }, }, }, },
      have hfp : f'.fun_value p = f.fun_value k, symmetry, apply fun_value_def f'into.left,
        simp only [mem_union, mem_insert, mem_singleton], finish,
      have hfk : f'.fun_value k = k, symmetry, apply fun_value_def f'into.left,
        simp only [mem_union, mem_insert, mem_singleton], finish,
      have hfo : ∀ {n : Set}, n ≠ p → n ∈ k → f'.fun_value n = f.fun_value n,
        intros l hlp hlk, symmetry, apply fun_value_def f'into.left,
        simp only [mem_union, mem_insert, mem_singleton, mem_diff],
        refine or.inr ⟨fun_value_def' hinto.left _, _⟩,
        { rw hinto.right.left, exact self_sub_succ hlk, },
        { rintro (hor|hor),
          { exact hlp (pair_inj hor).left, },
          { apply nat_not_mem_self hk,
            suffices hlke : l = k,
              nth_rewrite 0 ←hlke, exact hlk,
            apply from_one_to_one hinto.left hoto,
            { rw hinto.right.left, exact self_sub_succ hlk, },
            { rw hinto.right.left, exact self_mem_succ, },
            exact (pair_inj hor).right, }, },
      have hor : ∀ {n : Set}, n ∈ k.succ → n = p ∨ n = k ∨ n ≠ p ∧ n ∈ k,
        intros m hmk, by_cases ho : m = p,
        { exact or.inl ho, },
        { rw [mem_succ_iff_mem, le_iff] at hmk, cases hmk,
          { exact or.inr (or.inr ⟨ho, hmk⟩), },
          { exact or.inr (or.inl hmk), }, },
      have f'oto : f'.one_to_one,
        apply one_to_one_of f'into.left, simp only [f'into.right.left],
        intros m hm n hn hne hmn, apply hne,
        obtain (horm|horm|horm) := hor hm; obtain (horn|horn|horn) := hor hn,
        { rw [horm, horn], },
        { exfalso, apply nat_not_mem_self hk,
          suffices hkp : k = p,
            nth_rewrite 0 hkp, exact hp,
          apply from_one_to_one hinto.left hoto,
          { rw hinto.right.left, exact self_mem_succ, },
          { rw [hinto.right.left, ←horm], exact hm, },
          rw [←hfp, ←horm, hmn, horn, hfk, ←he, horm], },
        { exfalso, apply nat_not_mem_self hk,
          suffices hkn : k = n,
            nth_rewrite 0 hkn, exact horn.right,
          apply from_one_to_one hinto.left hoto,
          { rw hinto.right.left, exact self_mem_succ, },
          { rw hinto.right.left, exact hn, },
          rw [←hfp, ←horm, hmn, hfo horn.left horn.right], },
        { exfalso, apply nat_not_mem_self hk,
          suffices hkp : k = p,
            nth_rewrite 0 hkp, exact hp,
          apply from_one_to_one hinto.left hoto,
          { rw hinto.right.left, exact self_mem_succ, },
          { rw [hinto.right.left, ←horn], exact hn, },
          rw [←hfp, ←horn, ←hmn, horm, hfk, ←he, horn], },
        { rw [horm, horn], },
        { exfalso, apply horn.left,
          apply from_one_to_one hinto.left hoto,
          { rw hinto.right.left, exact hn, },
          { rw hinto.right.left, exact self_sub_succ hp, },
          rw [he, ←hfk, ←horm, hmn, hfo horn.left horn.right], },
        { exfalso, apply nat_not_mem_self hk,
          suffices hkn : k = m,
            nth_rewrite 0 hkn, exact horm.right,
          apply from_one_to_one hinto.left hoto,
          { rw hinto.right.left, exact self_mem_succ, },
          { rw hinto.right.left, exact hm, },
          rw [←hfp, ←horn, ←hmn, hfo horm.left horm.right], },
        { exfalso, apply horm.left,
          apply from_one_to_one hinto.left hoto,
          { rw hinto.right.left, exact hm, },
          { rw hinto.right.left, exact self_sub_succ hp, },
          rw [he, ←hfk, ←horn, ←hmn, hfo horm.left horm.right], },
        { apply from_one_to_one hinto.left hoto,
          { rw hinto.right.left, exact hm, },
          { rw hinto.right.left, exact hn, },
          rw [←hfo horm.left horm.right, ←hfo horn.left horn.right, hmn], },
      have f'cl : ∀ {n : Set}, n ∈ k → f'.fun_value n ∈ k,
        intros n hnk, by_cases hnp : n = p,
        { rw [hnp, hfp], specialize hr self_mem_succ, rw [mem_succ_iff_mem, le_iff] at hr, cases hr,
          { exact hr, },
          { exfalso, nth_rewrite 1 ←he at hr,
            suffices hkp : k = p, rw ←hkp at hp, exact nat_not_mem_self hk hp,
            apply from_one_to_one hinto.left hoto,
            { rw hinto.right.left, exact self_mem_succ, },
            { rw hinto.right.left, exact self_sub_succ hp, },
            exact hr, }, },
        { rw hfo hnp hnk, specialize hr (self_sub_succ hnk), rw [mem_succ_iff_mem, le_iff] at hr, cases hr,
          { exact hr, },
          { exfalso, rw ←he at hr, apply hnp, apply from_one_to_one hinto.left hoto,
            { rw hinto.right.left, exact self_sub_succ hnk, },
            { rw hinto.right.left, exact hps, },
            exact hr, }, },
      have freq : f'.ran = f.ran, rw eq_iff_subset_and_subset, split,
      { intro y, simp only [mem_ran_iff hinto.left, mem_ran_iff f'into.left, hinto.right.left, f'into.right.left],
        rintro ⟨n, hn, hm⟩, obtain (hnp|hnk|⟨hnp,hnk⟩) := hor hn,
        { rw [hnp, hfp] at hm, exact ⟨_, self_mem_succ, hm⟩, },
        { rw [hnk, hfk, ←he] at hm, exact ⟨_, self_sub_succ hp, hm⟩, },
        { rw hfo hnp hnk at hm, exact ⟨_, hn, hm⟩, }, },
      { rw hcaseI f'into f'oto @f'cl, exact hinto.right.right, },
      rw ←freq, exact hcaseI f'into f'oto @f'cl, },
    { replace hc : ∀ {n : Set}, n ∈ k → f.fun_value n ∈ k,
        intros n hn,
        have ho : f.fun_value n ∈ k ∨ f.fun_value n = k, rw [←le_iff, ←mem_succ_iff_mem],
          apply hinto.right.right, apply fun_value_def'' hinto.left, rw hinto.right.left,
          rw [mem_succ_iff_mem, le_iff], finish,
        cases ho,
        { assumption, },
        { exfalso, exact hc ⟨_, hn, ho⟩, },
      exact hcaseI hinto hoto @hc, }, },
end

-- Corollary 6C
theorem pigeonhole' : ¬ ∃ A : Set, A.is_finite ∧ ∃ B : Set, B ⊂ A ∧ A.equinumerous B :=
begin
  rintro ⟨A, ⟨n, hn, g, hfin⟩, B, hBA, f, heq⟩,
  let H : Set := g.comp (f.comp g.inv),
  have Hoto : H.one_to_one, refine comp_one_to_one hfin.oto (comp_one_to_one heq.oto _),
    rw ←T3F_b hfin.onto.left.left, exact hfin.onto.left,
  have Hdom : H.dom = n,
    have h : g.inv.ran = f.dom, rw [T3E_b, heq.onto.right.left, hfin.onto.right.left],
    have hl : g.inv.ran ⊆ f.dom, rw h, exact subset_self,
    have hr : f.dom ⊆ g.inv.ran, rw h, exact subset_self,
    have h' : (f.comp g.inv).ran ⊆ g.dom, rw [ran_comp hr, heq.onto.right.right, hfin.onto.right.left], exact hBA.left,
    rw [dom_comp h', dom_comp hl, T3E_a, hfin.onto.right.right],
  have Hran : H.ran ⊆ n, rw ←hfin.onto.right.right, exact ran_comp_sub,
  have Hfun : H.is_function, apply T3H_a hfin.onto.left, apply T3H_a heq.onto.left,
    rw T3F_a, exact hfin.oto,
  have hr : H.ran ⊂ n, refine ⟨Hran, λ he, _⟩,
    have hex : ∃ x, x ∈ A ∧ x ∉ B, apply classical.by_contradiction, intro h, apply hBA.right,
      rw eq_iff_subset_and_subset, refine ⟨hBA.left, λ x hx, _⟩,
      apply classical.by_contradiction, intro hnx, apply h,
      exact ⟨_, hx, hnx⟩,
    rcases hex with ⟨a, hA, hB⟩,
    have h : g.fun_value a ∉ H.ran, intro h, apply hB, rw mem_ran_iff Hfun at h, rcases h with ⟨x, hn, ho⟩,
      rw T3H_c hfin.onto.left (T3H_a heq.onto.left (T3F_a.mpr hfin.oto)) _ at ho,
      have h : (f.comp g.inv).ran = B, rw ←heq.onto.right.right, apply ran_comp,
        rw [T3E_b, hfin.onto.right.left, heq.onto.right.left], exact subset_self,
      have hax : a = (f.comp g.inv).fun_value x, apply from_one_to_one hfin.onto.left hfin.oto,
        { rw hfin.onto.right.left, exact hA, },
        { rw hfin.onto.right.left,
          have h : (f.comp g.inv).ran = B, rw ←heq.onto.right.right, apply ran_comp,
            rw [T3E_b, hfin.onto.right.left, heq.onto.right.left], exact subset_self,
          apply hBA.left, rw ←h, apply fun_value_def'' (T3H_a heq.onto.left (T3F_a.mpr hfin.oto)),
          rw dom_comp, rw [T3E_a, hfin.onto.right.right], rw ←Hdom, exact hn,
          rw [T3E_b, hfin.onto.right.left, heq.onto.right.left], exact subset_self, },
        exact ho,
      rw [hax, ←h], apply fun_value_def'' (T3H_a heq.onto.left (T3F_a.mpr hfin.oto)),
      rw dom_comp, rw [T3E_a, hfin.onto.right.right], rw ←Hdom, exact hn,
      rw [T3E_b, hfin.onto.right.left, heq.onto.right.left], exact subset_self,
      exact hn,
      apply h, rw he, rw ←hfin.onto.right.right, apply fun_value_def'' hfin.onto.left, rw hfin.onto.right.left, exact hA,
  apply pigeonhole hn hr,
  exact ⟨H, ⟨Hfun, Hdom, rfl⟩, Hoto⟩,
end

-- Corollary 6D part a
theorem pigeonhole'' {A B : Set} (hBA : B ⊂ A) (heq : A.equinumerous B) : ¬ A.is_finite :=
begin
  intro hf, apply pigeonhole', exact ⟨A, hf, B, hBA, heq⟩,
end

-- Corollary 6D part b
theorem nat_infinite : ¬ (ω : Set).is_finite :=
begin
  have h : ∅ ∉ succ_fun.ran := succ_not_onto,
  have hr : succ_fun.ran ⊂ ω, refine ⟨succ_fun_into_fun.right.right, _⟩,
    intro he, apply h, rw he, exact nat_induct.zero,
  exact pigeonhole'' hr ⟨succ_fun, ⟨succ_fun_into_fun.left, succ_fun_into_fun.right.left, rfl⟩, succ_one_to_one⟩,
end

-- Corollary 6D part c
theorem exists_unique_equiv_nat_of_finite {A : Set} (hf : A.is_finite) : ∃! n : Set, n ∈ ω ∧ A.equinumerous n :=
begin
  apply exists_unique_of_exists_of_unique hf, rintros n m ⟨hn, hAn⟩ ⟨hm, hAm⟩,
  have hnmeq : n.equinumerous m := equin_trans (equin_symm hAn) hAm,
  apply classical.by_contradiction, intro hne,
  cases nat_order_lin.conn hn hm hne with hnm hnm; rw [nat_order, pair_mem_pair_sep] at hnm; rcases hnm with ⟨-, -, hnm⟩,
  { rw ←nat_ssub_iff_mem hn hm at hnm, exact pigeonhole'' hnm (equin_symm hnmeq) ⟨_, hm, equin_refl⟩, },
  { rw ←nat_ssub_iff_mem hm hn at hnm, exact pigeonhole'' hnm hnmeq ⟨_, hn, equin_refl⟩, },
end

-- problem 20
theorem exists_desc_chain_of_no_least {A : Set} (hA : A ≠ ∅) {R : Set} (hR : R.is_rel) (h : ∀ x ∈ A, ∃ y : Set, y ∈ A ∧ y.pair x ∈ R) :
∃ f : Set, f.into_fun ω A ∧ ∀ ⦃n : Set⦄, n ∈ ω → (f.fun_value n.succ).pair (f.fun_value n) ∈ R :=
begin
  let S : Set := pair_sep (λ x y : Set, y.pair x ∈ R) A A,
  have domS : S.dom = A, rw eq_iff_subset_and_subset, split,
      exact pair_sep_dom_sub,
    intros x hx, obtain ⟨y, hy, hyx⟩ := h _ hx, rw mem_dom, use y, rw pair_mem_pair_sep,
    exact ⟨hx, hy, hyx⟩,
  obtain ⟨g, gfun, gsub, gdom⟩ := @ax_ch_1 S pair_sep_is_rel,
  have ginto : g.into_fun A A, refine ⟨gfun, _, _⟩,
      rw [gdom, domS],
    intro y, rw mem_ran, rintro ⟨x, hxy⟩, replace hxy := gsub hxy, rw pair_mem_pair_sep at hxy,
    exact hxy.right.left,
  obtain ⟨a, ha⟩ := inhabited_of_ne_empty hA,
  let f : Set := A.rec_fun a g,
  refine ⟨f, rec_fun_into_fun ha ginto, λ n hn, _⟩,
  have he := (recursion_thm ha ginto).right _ hn, rw he,
  suffices h : (f.fun_value n).pair (g.fun_value ((A.rec_fun a g).fun_value n)) ∈ S,
    rw pair_mem_pair_sep at h, exact h.right.right,
  apply gsub, apply fun_value_def' ginto.left, rw [gdom, domS], apply @rec_fun_ran A a g,
  apply fun_value_def'' (rec_fun_is_fun ha), rw rec_fun_dom_eq_nat ha ginto, exact hn,
end

def dominated (A B : Set) : Prop := ∃ f : Set, f.into_fun A B ∧ f.one_to_one
infix ≼ := dominated
lemma dominated_iff {A B : Set} : A ≼ B ↔ ∃ C : Set, C ⊆ B ∧ A.equinumerous C :=
begin
  split,
  { rintro ⟨f, finto, foto⟩, exact ⟨_, finto.right.right, _, onto_ran_of_into finto, foto⟩, },
  { rintro ⟨C, hCB, f, fonto, foto⟩, exact ⟨_, into_of_onto_ran_sub hCB fonto, foto⟩, },
end

end Set