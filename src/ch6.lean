import ch4

universe u

namespace Set

reserve infix ` ≈ `:50
reserve infix ` ≉ `:50
reserve infix ` ≼ `:50

structure correspondence (A B f : Set) : Prop :=
(onto : f.onto_fun A B)
(oto : f.one_to_one)

def equinumerous (A B : Set) : Prop := ∃ f : Set, A.correspondence B f
infix ≈ := equinumerous
infix ≉ := (λ A B : Set, ¬(A ≈ B))

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

-- Theorem 6A part b
theorem equin_symm {A B : Set} (heq : A.equinumerous B) : B.equinumerous A :=
begin
  rcases heq with ⟨F, honto, hoto⟩,
  refine ⟨F.inv, ⟨T3F_a.mpr hoto, _, _⟩, _⟩,
  { rw ←honto.right.right, exact T3E_a, },
  { rw ←honto.right.left, exact T3E_b, },
  { exact (T3F_b honto.left.left).mp honto.left, },
end

-- Theorem 6A part c
theorem equin_trans {A B C : Set} (hAB : A.equinumerous B) (hBC : B.equinumerous C) : A.equinumerous C :=
begin
  rcases hAB with ⟨F, hF, hF'⟩,
  rcases hBC with ⟨G, hG, hG'⟩,
  have hf : (G.comp F).is_function := T3H_a hG.left hF.left,
  have hd : (G.comp F).dom = F.dom,
    rw T3H_b hG.left hF.left, apply ext, intro x,
    rw [mem_sep, hG.right.left, hF.right.left, and_iff_left_iff_imp, ←hF.right.left, ←hF.right.right],
    exact fun_value_def'' hF.left,
  refine ⟨G.comp F, ⟨hf, _, _⟩, _⟩,
  { rw hd, exact hF.right.left, },
  { apply ext, intro z,
    simp only [mem_ran_iff hf, ←hG.right.right, mem_ran_iff hG.left, hG.right.left, ←hF.right.right, mem_ran_iff hF.left, hd], split,
    { rintro ⟨x, hx, he⟩, refine ⟨F.fun_value x, ⟨_, hx, rfl⟩, _⟩, rw ←T3H_c hG.left hF.left, assumption, rw hd, assumption, },
    { rintro ⟨y, ⟨x, hx, he⟩, he'⟩, refine ⟨x, hx, _⟩, rw T3H_c hG.left hF.left, rw ←he, assumption, rw hd, assumption, }, },
  { apply one_to_one_of hf, intros x hx x' hx' hne he, apply hne,
    rw [T3H_c hG.left hF.left hx, T3H_c hG.left hF.left hx'] at he,
    apply from_one_to_one hF.left hF', rw ←hd, assumption, rw ←hd, assumption,
    apply from_one_to_one hG.left hG',
    { rw [hG.right.left, ←hF.right.right], apply fun_value_def'' hF.left, rw ←hd, assumption, },
    { rw [hG.right.left, ←hF.right.right], apply fun_value_def'' hF.left, rw ←hd, assumption, },
    assumption, },
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

-- postponed til chapter 7
-- TODO:
noncomputable constant card : Set.{u} → Set.{u}
axiom card_equiv : ∀ {A B : Set}, A.card = B.card ↔ A.equinumerous B
axiom card_finite : ∀ {A : Set}, A.is_finite → A.card ∈ ω ∧ A.equinumerous (A.card)

def is_cardinal (N : Set) : Prop := ∃ A : Set, A.card = N

-- to be proved at end of chapter 7
theorem card_of_cardinal_eq_self {κ : Set} (h : κ.is_cardinal) : κ.card = κ := sorry

lemma card_nat {n : Set} (hn : n ∈ ω) : n.card = n :=
have hf : n.is_finite := ⟨n, hn, equin_refl⟩,
unique_of_exists_unique (exists_unique_equiv_nat_of_finite hf) (card_finite hf) ⟨hn, equin_refl⟩

lemma finite_iff {A : Set} : A.is_finite ↔ ∃ n : Set, n ∈ ω ∧ A.card = n :=
begin
  simp only [is_finite, ←card_equiv, subst_right_of_and card_nat],
end

lemma nat_finite {n : Set} (hn : n ∈ ω) : n.is_finite := finite_iff.mpr ⟨_, hn, card_nat hn⟩

theorem nat_is_cardinal {n : Set} (hn : n ∈ ω) : n.is_cardinal := ⟨_, card_nat hn⟩

theorem card_omega_not_nat : ¬ ∃ n : Set, n ∈ ω ∧ card ω = n :=
begin
  rintro ⟨n, hn, he⟩, apply nat_infinite, rw [←card_nat hn, card_equiv] at he, exact ⟨_, hn, he⟩,
end

notation `ℵ₀` := card ω

lemma not_empty_of_card_not_empty {κ : Set} (hnz : κ ≠ ∅) {X : Set} (he : X.card = κ) : X ≠ ∅ :=
begin
  intro hee, rw [hee, card_nat (nat_induct.zero)] at he, apply hnz, rw he,
end

lemma prod_singleton_equin {X Y : Set} : X.equinumerous (X.prod {Y}) :=
begin
    let f : Set := pair_sep (λ a b, b = a.pair Y) X (X.prod {Y}),
    have ffun : f.is_function := pair_sep_eq_is_fun,
    have fdom : f.dom = X, apply pair_sep_eq_dom_eq, intros a ha,
      simp only [mem_prod, exists_prop, mem_singleton], exact ⟨_, ha, _, rfl, rfl⟩,
    have fran : f.ran = X.prod {Y}, apply pair_sep_eq_ran_eq, intros b hb,
      simp only [mem_prod, exists_prop, mem_singleton] at hb, rcases hb with ⟨a, ha, b', hb', hp⟩, rw hb' at hp,
      exact ⟨_, ha, hp⟩,
    have foto : f.one_to_one, apply pair_sep_eq_oto, intros a  ha a' ha' he, exact (pair_inj he).left,
    exact ⟨_, ⟨ffun, fdom, fran⟩, foto⟩,
end

lemma singleton_equin {x y : Set} : equinumerous {x} {y} :=
⟨{x.pair y}, single_pair_onto, single_pair_oto⟩

lemma prod_disj_of_right_disj {A B C D : Set} (h : C ∩ D = ∅) : A.prod C ∩ B.prod D = ∅ :=
begin
  rw rel_eq_empty (inter_rel_is_rel prod_is_rel), simp [mem_inter, pair_mem_prod],
  intros x y hA hC hB hD, apply mem_empty y, rw [←h, mem_inter], exact ⟨hC, hD⟩,
end

lemma prod_union {A B C : Set} : A.prod (B ∪ C) = (A.prod B) ∪ (A.prod C) :=
begin
  apply rel_eq prod_is_rel (union_rel_is_rel prod_is_rel prod_is_rel),
  simp only [pair_mem_prod, and_or_distrib_left, mem_union, forall_const, iff_self],
end

lemma prod_empty_eq_empty {A : Set} : A.prod ∅ = ∅ :=
begin
  rw rel_eq_empty prod_is_rel, intros x y h, rw pair_mem_prod at h, exact mem_empty _ h.right,
end

-- excercise 6
theorem card_not_set {κ : Set} (hc : κ.is_cardinal) (hnz : κ ≠ ∅) : ¬ ∃ Κ : Set, ∀ X : Set, X ∈ Κ ↔ card X = κ :=
begin
  rintro ⟨Κ, h⟩, apply univ_not_set,
  existsi Κ.Union.Union.Union, intro X,
  rcases hc with ⟨Y, hY⟩,
  let Z : Set := Y.prod {X},
  have hZ : Z ∈ Κ, rw [h _, ←hY, card_equiv], apply equin_symm, exact prod_singleton_equin,
  have hin : Y.inhab := inhabited_of_ne_empty (not_empty_of_card_not_empty hnz hY),
  rcases hin with ⟨u, hu⟩,
  simp only [mem_Union, exists_prop], refine ⟨{u, X}, ⟨u.pair X, ⟨Z, hZ, _⟩, _⟩, _⟩,
  { simp only [mem_prod, exists_prop, mem_singleton], exact ⟨_, hu, _, rfl, rfl⟩, },
  { rw [pair, mem_insert, mem_singleton], exact or.inr rfl, },
  { rw [mem_insert, mem_singleton], exact or.inr rfl, },
end

def finite_cardinal (κ : Set) : Prop := ∃ X : Set, X.is_finite ∧ card X = κ

theorem one_finite_all_finite {κ : Set} (hf : κ.finite_cardinal) {X : Set} (hc : card X = κ) : X.is_finite :=
begin
  rcases hf with ⟨X', ⟨n, hn, hX'n⟩, hc'⟩, rw [←hc', card_equiv] at hc, exact ⟨_, hn, equin_trans hc hX'n⟩
end

theorem finite_cardinals_iff_nat {X : Set} : X.finite_cardinal ↔ X ∈ ω :=
begin
  simp only [finite_cardinal, is_finite], split,
  { rintro ⟨Y, ⟨n, hn, hYn⟩, hc⟩, rw ←card_equiv at hYn, rw [hYn, card_nat hn] at hc, rw ←hc, exact hn, },
  { rintro hX, refine ⟨X, ⟨X, hX, equin_refl⟩, card_nat hX⟩, },
end

theorem aleph_null_infinite_cardinal : ¬ finite_cardinal ℵ₀ :=
begin
  rintro ⟨X, ⟨n, hn, hXn⟩, hc⟩, apply nat_infinite, rw [card_equiv] at hc, refine ⟨_, hn, equin_trans (equin_symm hc) hXn⟩,
end

lemma Lemma_6F : ∀ {n : Set}, n ∈ ω → ∀ {C : Set}, C ⊂ n → ∃ m : Set, m ∈ n ∧ C.equinumerous m :=
begin
  apply @induction (λ n, ∀ {C : Set}, C ⊂ n → ∃ m : Set, m ∈ n ∧ C.equinumerous m),
  { rintros C ⟨hs, hne⟩, exfalso, apply hne, rw eq_iff_subset_and_subset, refine ⟨hs, λ x hx, _⟩, exfalso, exact mem_empty _ hx, },
  { intros k hk hi C hCk, by_cases heCk : C = k,
    { refine ⟨_, self_mem_succ, _⟩, rw heCk, exact equin_refl, },
    { by_cases hkmC : k ∈ C,
      { have hCe : C = (C ∩ k) ∪ {k}, apply ext, simp only [mem_union, mem_inter, mem_singleton], intro x, split,
        { intro hxC,
          have hxk : x ∈ k.succ := hCk.left hxC,
          rw [mem_succ_iff_mem, le_iff] at hxk, cases hxk,
          { left, exact ⟨hxC, hxk⟩, },
          { right, exact hxk, }, },
        { rintro (⟨hxC, hxk⟩|hxk),
          { exact hxC, },
          { rw ←hxk at hkmC, exact hkmC, }, },
        have hCkp : C ∩ k ⊂ k, refine ⟨λ x hx, _, _⟩,
          { rw mem_inter at hx, exact hx.right, },
          { intro hCke, apply hCk.right, rw eq_iff_subset_and_subset, refine ⟨hCk.left, λ x hxk, _⟩,
            rw [mem_succ_iff_mem, le_iff] at hxk, cases hxk,
            { rw ←hCke at hxk, rw mem_inter at hxk, exact hxk.left, },
            { rw ←hxk at hkmC, exact hkmC, }, },
        specialize hi hCkp, rcases hi with ⟨m, hmk, f, fonto, foto⟩,
        let g : Set := f ∪ {k.pair m},
        have ginto : g.into_fun C m.succ, rw fun_def_equiv,
          have hf : (C ∩ k).is_func m f, rw ←fun_def_equiv, exact into_of_onto fonto,
          refine ⟨λ p hp, _, λ x hxC, _⟩,
          { simp only [mem_prod, exists_prop, mem_succ_iff_mem, le_iff], rw [mem_union, mem_singleton] at hp,
            cases hp,
            { replace hp := hf.left hp, simp only [mem_prod, exists_prop] at hp,
              rcases hp with ⟨x, hx, y, hy, hp⟩, rw mem_inter at hx, exact ⟨_, hx.left, _, or.inl hy, hp⟩, },
            { exact ⟨_, hkmC, _, or.inr rfl, hp⟩, }, },
          { rw [hCe, mem_union, mem_singleton] at hxC, simp only [mem_union, mem_singleton], cases hxC,
            { have he : ∃ y : Set, x.pair y ∈ f := exists_of_exists_unique (hf.right _ hxC),
              rcases he with ⟨y, hxyf⟩, refine exists_unique_of_exists_of_unique ⟨_, or.inl hxyf⟩ _,
              rintros z z' (hz|hz) (hz'|hz'),
              { exact unique_of_exists_unique (hf.right _ hxC) hz hz', },
              { exfalso, rw mem_inter at hxC, rw (pair_inj hz').left at hxC, exact nat_not_mem_self hk hxC.right, },
              { exfalso, rw mem_inter at hxC, rw (pair_inj hz).left at hxC, exact nat_not_mem_self hk hxC.right, },
              { rw [(pair_inj hz).right, (pair_inj hz').right], }, },
            { rw hxC, refine ⟨_, or.inr rfl, _⟩, rintros y (hy|hy),
              { exfalso, apply nat_not_mem_self hk,
                have hkd : k ∈ f.dom, rw mem_dom, exact ⟨_, hy⟩,
                rw [fonto.right.left, mem_inter] at hkd, exact hkd.right, },
              { exact (pair_inj hy).right, }, }, },
        have gran : g.ran = m.succ, rw [ran_union, fonto.right.right, ran_single_pair, succ], rw union_comm,
        have goto : g.one_to_one, apply union_one_to_one foto single_pair_oto, rw [fonto.right.right, ran_single_pair],
          rw eq_empty, intros x hx, rw [mem_inter, mem_singleton] at hx, apply nat_not_mem_self ((mem_nat_iff hk).mp hmk).left,
          cases hx with hxmm hxem, rw hxem at hxmm, exact hxmm,
        existsi m.succ, rw ←mem_iff_succ_mem_succ, exact ⟨hmk, _, ⟨ginto.left, ginto.right.left, gran⟩, goto⟩,
        exact ((mem_nat_iff hk).mp hmk).left, exact hk, },
      { have hCpk : C ⊂ k, refine ⟨λ x hxC, _, heCk⟩,
          have hxk : x ∈ k.succ := hCk.left hxC,
          rw [mem_succ_iff_mem, le_iff] at hxk, cases hxk,
          { exact hxk, },
          { exfalso, rw hxk at hxC, exact hkmC hxC, },
        specialize hi hCpk, rcases hi with ⟨m, hmk, hCm⟩,
        simp only [mem_succ_iff_mem, le_iff], exact ⟨_, or.inl hmk, hCm⟩, }, }, },
end

-- Corollary 6G
theorem subset_finite_of_finite {A : Set.{u}} (hA : A.is_finite) {B : Set} (hBA : B ⊆ A) : B.is_finite :=
begin
  by_cases he : A = B,
  { rw ←he, exact hA, },
  { rcases hA with ⟨n, hn, f, fonto, foto⟩,
    have hBeq : B.equinumerous (f.img B),
      let g : Set := f.restrict B,
      have gfun : g.is_function := restrict_is_function fonto.left,
      have gdom : g.dom = B, refine restrict_dom _, rw fonto.right.left, exact hBA,
      have gran : g.ran = f.img B := restrict_ran,
      have goto : g.one_to_one, refine restrict_one_to_one fonto.left foto _, rw fonto.right.left, exact hBA,
      exact ⟨_, ⟨gfun, gdom, gran⟩, goto⟩,
    have hfimgne : f.img B ≠ n, rw ←fonto.right.right, refine img_ne_ran_of_ne_dom fonto.left foto _ _,
      { rw fonto.right.left, exact hBA, },
      rw fonto.right.left, symmetry, exact he,
    have hfimgsub : f.img B ⊆ n, rw ←fonto.right.right, exact img_subset_ran,
    obtain ⟨m, hmn, hfimgeqm⟩ := Lemma_6F hn ⟨hfimgsub, hfimgne⟩,
    have hm : m ∈ (ω : Set.{u}) := ((mem_nat_iff hn).mp hmn).left,
    exact ⟨_, hm, equin_trans hBeq hfimgeqm⟩, },
end

-- All of the excericises at the end of the section on finite sets are worth doing

theorem T6H_a {K₁ K₂ : Set} (hK : K₁.equinumerous K₂) {L₁ L₂ : Set} (hL : L₁.equinumerous L₂) (hd₁ : K₁ ∩ L₁ = ∅) (hd₂ : K₂ ∩ L₂ = ∅) : (K₁ ∪ L₁).equinumerous (K₂ ∪ L₂) :=
begin
  rcases hK with ⟨f, fonto, foto⟩,
  rcases hL with ⟨g, gonto, goto⟩,
  let h : Set := f ∪ g,
  have honto : h.onto_fun (K₁ ∪ L₁) (K₂ ∪ L₂), rw [←fonto.right.left, ←gonto.right.left, ←fonto.right.right, ←gonto.right.right],
    apply union_fun fonto.left gonto.left,
    rw [fonto.right.left, gonto.right.left], exact hd₁,
  have hoto : h.one_to_one, apply union_one_to_one foto goto,
    rw [fonto.right.right, gonto.right.right], exact hd₂,
  exact ⟨h, honto, hoto⟩,
end

theorem T6H_b {K₁ K₂ : Set} (hK : K₁.equinumerous K₂) {L₁ L₂ : Set} (hL : L₁.equinumerous L₂) : (K₁.prod L₁).equinumerous (K₂.prod L₂) :=
begin
  rcases hK with ⟨f, fonto, foto⟩,
  rcases hL with ⟨g, gonto, goto⟩,
  let h : Set := pair_sep (λ a b, b = (f.fun_value a.fst).pair (g.fun_value a.snd)) (K₁.prod L₁) (K₂.prod L₂),
  have hfun : h.is_function := pair_sep_eq_is_fun,
  have hdom : h.dom = K₁.prod L₁, apply pair_sep_eq_dom_eq, intros z hz,
    rw [pair_mem_prod, ←fonto.right.right, ←gonto.right.right], split,
    { apply fun_value_def'' fonto.left, rw fonto.right.left, exact (fst_snd_mem_dom_ran hz).left, },
    { apply fun_value_def'' gonto.left, rw gonto.right.left, exact (fst_snd_mem_dom_ran hz).right, },
  have hran : h.ran = K₂.prod L₂, apply pair_sep_eq_ran_eq, intros b hb, rw mem_prod at hb,
    rcases hb with ⟨k, hk, l, hl, hb⟩,
    rw [←fonto.right.right, mem_ran_iff fonto.left] at hk, rw [←gonto.right.right, mem_ran_iff gonto.left] at hl,
    rcases hk with ⟨k', hk', hk⟩, rcases hl with ⟨l', hl', hl⟩,
    refine ⟨k'.pair l', _, _⟩,
    { rw pair_mem_prod, rw [←fonto.right.left, ←gonto.right.left], finish, },
    { rw [fst_congr, snd_congr, hb, hk, hl], },
  have hoto : h.one_to_one, apply pair_sep_eq_oto, intros p hp q hq he,
    have he' := pair_inj he,
    rw [fst_snd_spec (is_pair_of_mem_prod hp), fst_snd_spec (is_pair_of_mem_prod hq)],
    have feq : p.fst = q.fst, refine from_one_to_one fonto.left foto _ _ he'.left,
      { rw fonto.right.left, exact (fst_snd_mem_dom_ran hp).left, },
      { rw fonto.right.left, exact (fst_snd_mem_dom_ran hq).left, },
    have seq : p.snd = q.snd, refine from_one_to_one gonto.left goto _ _ he'.right,
      { rw gonto.right.left, exact (fst_snd_mem_dom_ran hp).right, },
      { rw gonto.right.left, exact (fst_snd_mem_dom_ran hq).right, },
    rw [feq, seq],
  exact ⟨_, ⟨hfun, hdom, hran⟩, hoto⟩,
end

theorem T6H_c {K₁ K₂ : Set} (hK : K₁.equinumerous K₂) {L₁ L₂ : Set} (hL : L₁.equinumerous L₂) : (L₁.into_funs K₁).equinumerous (L₂.into_funs K₂) :=
begin
  rcases hK with ⟨f, fonto, foto⟩,
  rcases hL with ⟨g, gonto, goto⟩,
  let H : Set := pair_sep (λ j h, h = f.comp (j.comp g.inv)) (L₁.into_funs K₁) (L₂.into_funs K₂),
  have Hfun : H.is_function := pair_sep_eq_is_fun,
  have Hdom : H.dom = L₁.into_funs K₁, apply pair_sep_eq_dom_eq, intros h hh, rw mem_into_funs at hh, rw mem_into_funs,
    apply comp_into_fun,
    { apply comp_into_fun (inv_into_fun gonto goto) hh, },
    { exact into_of_onto fonto, },
  have Hran : H.ran = L₂.into_funs K₂, apply pair_sep_eq_ran_eq, intros d hd, rw mem_into_funs at hd,
    let j := f.inv.comp (d.comp g), refine ⟨j, _, _⟩,
    { rw mem_into_funs, apply comp_into_fun,
      { apply comp_into_fun (into_of_onto gonto) hd, },
      { exact inv_into_fun fonto foto, }, },
    { rw [←Set.comp_assoc, ←Set.comp_assoc, eq_inv_id fonto.left foto, Set.comp_assoc, Set.comp_assoc, eq_inv_id gonto.left goto],
      rw [gonto.right.right, ←hd.right.left, comp_id hd.left, fonto.right.right], symmetry, exact id_comp hd.right.right hd.left, },
  have hoto : H.one_to_one, apply pair_sep_eq_oto, intros j hj j' hj' he,
    rw mem_into_funs at hj hj',
    have h : (f.comp (j.comp g.inv)).comp g = (f.comp (j'.comp g.inv)).comp g, rw he,
    rw [comp_assoc, comp_assoc, comp_assoc, comp_assoc, eq_id gonto.left goto, gonto.right.left] at h,
    nth_rewrite 0 ←hj.right.left at h, rw [←hj'.right.left, comp_id hj.left, comp_id hj'.left] at h,
    apply fun_ext hj.left hj'.left,
    { rw [hj.right.left, hj'.right.left], },
    { intros t ht, apply from_one_to_one fonto.left foto,
      { rw fonto.right.left, apply hj.right.right, apply fun_value_def'' hj.left ht, },
      { rw fonto.right.left, apply hj'.right.right, rw [hj.right.left, ←hj'.right.left] at ht,
        apply fun_value_def'' hj'.left ht, },
      { rw [←T3H_c fonto.left hj.left, ←T3H_c fonto.left hj'.left, h],
        { rw [dom_comp, hj'.right.left, ←hj.right.left], exact ht, rw [fonto.right.left], exact hj'.right.right, },
        { rw [dom_comp], exact ht, rw [fonto.right.left], exact hj.right.right, }, }, },
  exact ⟨_, ⟨Hfun, Hdom, Hran⟩, hoto⟩,
end

lemma same_card {A x : Set} : (A.prod {x}).card = A.card :=
begin
  rw card_equiv, apply equin_symm, exact prod_singleton_equin,
end

lemma disj {A B x y : Set} (hne : x ≠ y) : (A.prod {x}) ∩ (B.prod {y}) = ∅ :=
prod_disj (singleton_disj_of_ne hne)

lemma exists_add {κ μ : Set} : ∃ ν : Set, ∀ (K : Set), K.card = κ → ∀ (M : Set), M.card = μ → K ∩ M = ∅ → (K ∪ M).card = ν :=
begin
  let K' := κ.prod {∅},
  let M' := μ.prod {one},
  have hK' : K'.card = κ.card := same_card,
  have hM' : M'.card = μ.card := same_card,
  have hdisj : K' ∩ M' = ∅ := disj zero_ne_one,
  existsi (K' ∪ M').card, intros J hJ N hN hd,
  rw card_equiv, refine T6H_a _ _ hd hdisj,
  { rw [←card_equiv, hJ, hK', card_of_cardinal_eq_self ⟨_, hJ⟩], },
  { rw [←card_equiv, hN, hM', card_of_cardinal_eq_self ⟨_, hN⟩], },
end
lemma exists_mul {κ μ : Set} : ∃ ν : Set, ∀ (K : Set), K.card = κ → ∀ (M : Set), M.card = μ → (K.prod M).card = ν :=
begin
  existsi (κ.prod μ).card, intros K' hK' M' hM', rw card_equiv,
  apply T6H_b,
  { rw [←card_equiv, hK', card_of_cardinal_eq_self ⟨_, hK'⟩], },
  { rw [←card_equiv, hM', card_of_cardinal_eq_self ⟨_, hM'⟩], },
end
lemma exists_exp {κ μ : Set} : ∃ ν : Set, ∀ (K : Set), K.card = κ → ∀ (M : Set), M.card = μ → (M.into_funs K).card = ν :=
begin
  existsi (μ.into_funs κ).card, intros K' hK' M' hM', rw card_equiv,
  apply T6H_c,
  { rw [←card_equiv, hK', card_of_cardinal_eq_self ⟨_, hK'⟩], },
  { rw [←card_equiv, hM', card_of_cardinal_eq_self ⟨_, hM'⟩], },
end
lemma exists_add_fun : ∃ (add : Set → Set → Set), ∀ (κ μ : Set) (K : Set), K.card = κ → ∀ (M : Set), M.card = μ → K ∩ M = ∅ → (K ∪ M).card = add κ μ :=
choice_2_arg @exists_add
lemma exists_mul_fun : ∃ (mul : Set → Set → Set), ∀ (κ μ : Set) (K : Set), K.card = κ → ∀ (M : Set), M.card = μ → (K.prod M).card = mul κ μ :=
choice_2_arg @exists_mul
lemma exists_exp_fun : ∃ (exp : Set → Set → Set), ∀ (κ μ : Set) (K : Set), K.card = κ → ∀ (M : Set), M.card = μ → (M.into_funs K).card = exp κ μ :=
choice_2_arg @exists_exp
noncomputable def card_add : Set.{u} → Set.{u} → Set.{u} := classical.some exists_add_fun
noncomputable def card_mul : Set.{u} → Set.{u} → Set.{u} := classical.some exists_mul_fun
noncomputable def card_exp : Set.{u} → Set.{u} → Set.{u} := classical.some exists_exp_fun
lemma card_add_spec : ∀ {κ μ : Set} {K : Set}, K.card = κ → ∀ {M : Set}, M.card = μ → K ∩ M = ∅ → (K ∪ M).card = card_add κ μ :=
classical.some_spec exists_add_fun
lemma card_mul_spec : ∀ {κ μ : Set} {K : Set}, K.card = κ → ∀ {M : Set}, M.card = μ → (K.prod M).card = card_mul κ μ :=
classical.some_spec exists_mul_fun
lemma card_exp_spec : ∀ {κ μ : Set} {K : Set}, K.card = κ → ∀ {M : Set}, M.card = μ → (M.into_funs K).card = card_exp κ μ :=
classical.some_spec exists_exp_fun

-- example 6, page 141
theorem card_power {A : Set} : A.powerset.card = two.card_exp A.card :=
begin
  have h : A.powerset.card = (A.into_funs two).card, rw card_equiv, exact powerset_equinumerous_into_funs,
  rw h, apply card_exp_spec (card_nat two_nat) rfl,
end

-- example 7, page 142
theorem card_ne_power {κ : Set} (hκ : κ.is_cardinal) : κ ≠ two.card_exp κ :=
begin
  intro he, rcases hκ with ⟨K, hK⟩, rw [←hK, ←card_power, card_equiv] at he,
  exact not_equin_powerset he,
end

-- Theorem 6I part 1 part a
theorem card_add_comm {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) : κ.card_add μ = μ.card_add κ :=
begin
  rcases hκ with ⟨K, hK⟩,
  rcases hμ with ⟨M, hM⟩,
  let K' := K.prod {∅},
  let M' := M.prod {one},
  have hK' : K'.card = K.card := same_card,
  have hM' : M'.card = M.card := same_card,
  have hdisj : K' ∩ M' = ∅ := disj zero_ne_one,
  rw hK at hK', rw hM at hM', rw ←card_add_spec hK' hM' hdisj,
  rw inter_comm at hdisj, rw ←card_add_spec hM' hK' hdisj, rw union_comm,
end

-- Theorem 6I part 2 part a
theorem card_add_assoc {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) {ν : Set} (hν : ν.is_cardinal) :
κ.card_add (μ.card_add ν) = (κ.card_add μ).card_add ν :=
begin
  rcases hκ with ⟨K, hK⟩,
  rcases hμ with ⟨M, hM⟩,
  rcases hν with ⟨N, hN⟩,
  let K' := K.prod {∅},
  let M' := M.prod {one},
  let N' := N.prod {two},
  have hK' : K'.card = K.card := same_card,
  have hM' : M'.card = M.card := same_card,
  have hN' : N'.card = N.card := same_card,
  have hKM : K' ∩ M' = ∅ := disj zero_ne_one,
  have hKN : K' ∩ N' = ∅ := disj zero_ne_two,
  have hMN : M' ∩ N' = ∅ := disj one_ne_two,
  have hK_MN : K' ∩ (M' ∪ N') = ∅, rw [inter_union, hKM, hKN, union_empty],
  have hKM_N : (K' ∪ M') ∩ N' = ∅, rw [union_inter, hKN, hMN, union_empty],
  rw hK at hK', rw hM at hM', rw hN at hN',
  rw ←card_add_spec hM' hN' hMN,
  rw ←card_add_spec hK' rfl hK_MN,
  rw ←card_add_spec hK' hM' hKM,
  rw ←card_add_spec rfl hN' hKM_N,
  rw union_assoc,
end

-- Theorem 6I part 3
theorem card_mul_add {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) {ν : Set} (hν : ν.is_cardinal) :
κ.card_mul (μ.card_add ν) = (κ.card_mul μ).card_add (κ.card_mul ν) :=
begin
  rcases hκ with ⟨K, hK⟩,
  rcases hμ with ⟨M, hM⟩,
  rcases hν with ⟨N, hN⟩,
  let K' := K.prod {∅},
  let M' := M.prod {one},
  let N' := N.prod {two},
  have hK' : K'.card = K.card := same_card,
  have hM' : M'.card = M.card := same_card,
  have hN' : N'.card = N.card := same_card,
  have hKM : K' ∩ M' = ∅ := disj zero_ne_one,
  have hKN : K' ∩ N' = ∅ := disj zero_ne_two,
  have hMN : M' ∩ N' = ∅ := disj one_ne_two,
  have hK_MN : K' ∩ (M' ∪ N') = ∅, rw [inter_union, hKM, hKN, union_empty],
  have hKM_N : (K' ∪ M') ∩ N' = ∅, rw [union_inter, hKN, hMN, union_empty],
  rw hK at hK', rw hM at hM', rw hN at hN',
  rw ←card_add_spec hM' hN' hMN,
  rw ←card_mul_spec hK' rfl,
  rw ←card_mul_spec hK' hM',
  rw ←card_mul_spec hK' hN',
  rw ←card_add_spec rfl rfl (prod_disj_of_right_disj hMN),
  rw prod_union,
end

-- Theorem 6I part 4
theorem card_exp_add {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) {ν : Set} (hν : ν.is_cardinal) :
κ.card_exp (μ.card_add ν) = (κ.card_exp μ).card_mul (κ.card_exp ν) :=
begin
  rcases hκ with ⟨K, hK⟩,
  rcases hμ with ⟨M, hM⟩,
  rcases hν with ⟨N, hN⟩,
  let M' := M.prod {∅},
  let N' := N.prod {one},
  have hM' : M'.card = M.card := same_card,
  have hN' : N'.card = N.card := same_card,
  have hMN : M' ∩ N' = ∅ := disj zero_ne_one,
  rw hM at hM', rw hN at hN',
  rw ←card_add_spec hM' hN' hMN,
  rw ←card_exp_spec hK rfl,
  rw ←card_exp_spec hK hM',
  rw ←card_exp_spec hK hN',
  rw ←card_mul_spec rfl rfl,
  rw card_equiv,
  let f : Set := pair_sep_eq ((M' ∪ N').into_funs K) ((M'.into_funs K).prod (N'.into_funs K)) (λ g, (g.restrict M').pair (g.restrict N')),
  have hfun : f.is_function := pair_sep_eq_is_fun,
  have hdom : f.dom = (M' ∪ N').into_funs K, apply pair_sep_eq_dom_eq,
    intros g hg, simp only [pair_mem_prod, mem_into_funs], rw mem_into_funs at hg, split,
    { exact restrict_into_fun hg subset_union_left, },
    { exact restrict_into_fun hg subset_union_right, },
  have hran : f.ran = (M'.into_funs K).prod (N'.into_funs K), apply pair_sep_eq_ran_eq,
    intros p hp, simp only [mem_prod, exists_prop, mem_into_funs] at hp,
    rcases hp with ⟨g, hg, g', hg', he⟩, use g ∪ g', rw mem_into_funs,
    refine ⟨union_fun_into_fun hg hg' hMN, _⟩, rw he, congr,
    { symmetry, rw ←hg.right.left, apply restrict_union_eq hg.left.left, rw [hg.right.left, hg'.right.left], exact hMN, },
    { symmetry, rw [←hg'.right.left, union_comm], apply restrict_union_eq hg'.left.left, rw [hg.right.left, hg'.right.left], rw inter_comm, exact hMN, },
  have hoto : f.one_to_one, apply pair_sep_eq_oto, intros g hg g' hg' he, simp only [mem_into_funs] at hg hg',
    apply fun_ext hg.left hg'.left,
    { rw [hg.right.left, hg'.right.left], },
    intros i hi, rw [hg.right.left, mem_union] at hi, cases hi,
    { have hs : M' ⊆ g.dom, rw hg.right.left, exact subset_union_left,
      have hs' : M' ⊆ g'.dom, rw hg'.right.left, exact subset_union_left,
      rw ←@restrict_fun_value _ hg.left M' hs _ hi,
      rw ←@restrict_fun_value _ hg'.left M' hs' _ hi,
      rw (pair_inj he).left, },
    { have hs : N' ⊆ g.dom, rw hg.right.left, exact subset_union_right,
      have hs' : N' ⊆ g'.dom, rw hg'.right.left, exact subset_union_right,
      rw ←@restrict_fun_value _ hg.left N' hs _ hi,
      rw ←@restrict_fun_value _ hg'.left N' hs' _ hi,
      rw (pair_inj he).right, },
  exact ⟨_, ⟨hfun, hdom, hran⟩, hoto⟩,


end

lemma card_add_empty {κ : Set} (hκ : κ.is_cardinal) : κ.card_add ∅ = κ :=
begin
  rcases hκ with ⟨K, hK⟩,
  rw ←card_add_spec hK (card_nat zero_nat) inter_empty, rw union_empty, exact hK,
end

lemma T6J_a2 {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) : κ.card_add (μ.card_add one) = (κ.card_add μ).card_add one :=
card_add_assoc hκ hμ (nat_is_cardinal one_nat)

lemma card_mul_empty {κ : Set} (hκ : κ.is_cardinal) : κ.card_mul ∅ = ∅ :=
begin
  rcases hκ with ⟨K, hK⟩,
  rw ←card_mul_spec hK (card_nat zero_nat), rw prod_empty_eq_empty, exact card_nat zero_nat,
end

lemma T6J_m2 {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) : κ.card_mul (μ.card_add one) = (κ.card_mul μ).card_add κ :=
begin
  rw card_mul_add hκ hμ (nat_is_cardinal one_nat), congr,
  rcases hκ with ⟨K, hK⟩, rw ←card_mul_spec hK (card_nat one_nat), rw ←hK,
  rw [one, succ, union_empty], exact same_card,
end

lemma card_exp_empty {κ : Set} (hκ : κ.is_cardinal) : κ.card_exp ∅ = one :=
begin
  rcases hκ with ⟨K, hK⟩, rw ←card_exp_spec hK (card_nat zero_nat), rw ex2,
  have h : {∅} = one, rw [one, succ, union_empty],
  rw h, exact card_nat one_nat,
end
--set_option pp.notation false

lemma T6J_e2 {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) : κ.card_exp (μ.card_add one) = (κ.card_exp μ).card_mul κ :=
begin
  rw card_exp_add hκ hμ (nat_is_cardinal one_nat), congr,
  rcases hκ with ⟨K, hK⟩, rw [←card_exp_spec hK (card_nat one_nat), ←hK, card_equiv],
  let f : Set := pair_sep_eq (one.into_funs K) K (λ g, g.fun_value ∅),
  have hfun : f.is_function := pair_sep_eq_is_fun,
  have hdom : f.dom = one.into_funs K, apply pair_sep_eq_dom_eq,
    intros g hg, rw mem_into_funs at hg, apply hg.right.right, apply fun_value_def'' hg.left, rw [hg.right.left, one], exact self_mem_succ,
  have hran : f.ran = K, apply pair_sep_eq_ran_eq, intros x hx, use {(∅ : Set).pair x}, rw mem_into_funs,
      rw [one, succ, union_empty], refine ⟨single_pair_into hx, _⟩,
    symmetry, exact single_pair_fun_value,
  have hoto : f.one_to_one, apply pair_sep_eq_oto, intros g hg g' hg' he, rw Set.mem_into_funs at hg hg',
    apply fun_ext hg.left hg'.left,
      rw [hg.right.left, hg'.right.left],
    intros x hx, rw [hg.right.left, one, succ, union_empty, mem_singleton] at hx, rw hx, exact he,
  exact ⟨_, ⟨hfun, hdom, hran⟩, hoto⟩,
end

lemma card_add_one_eq_succ {n : Set} (hn : n.finite_cardinal) : n.card_add one = n.succ :=
begin
  rcases hn with ⟨N, hf, hN⟩, have hn := (card_finite hf).left, rw hN at hn,
  have h : card {n} = one, rw [←card_nat one_nat, card_equiv, one, succ, union_empty], exact singleton_equin,
  rw [←card_add_spec (card_nat hn) h, union_comm, ←succ],
    exact card_nat (nat_induct.succ_closed hn),
  simp only [eq_empty, mem_inter, mem_singleton],
  rintros k ⟨hk, he⟩, rw he at hk, exact nat_not_mem_self hn hk,
end

-- Theorem 6J
theorem card_add_eq_ord_add {m : Set} (hm : m.finite_cardinal) {n : Set} (hn : n.finite_cardinal) : m.card_add n = m + n :=
begin
  rw finite_cardinals_iff_nat at hm hn, revert n, apply induction,
    rw [card_add_empty (nat_is_cardinal hm), add_base hm],
  intros k hk hi,
  have hk' : k.finite_cardinal, rw finite_cardinals_iff_nat, exact hk,
  nth_rewrite 0 ←card_add_one_eq_succ hk',
  rw [T6J_a2 (nat_is_cardinal hm) (nat_is_cardinal hk), hi],
  have hmk : (m + k).finite_cardinal, rw finite_cardinals_iff_nat, exact add_into_nat hm hk,
  rw [card_add_one_eq_succ hmk, add_ind hm hk],
end

theorem card_mul_eq_ord_mul {m : Set} (hm : m.finite_cardinal) {n : Set} (hn : n.finite_cardinal) : m.card_mul n = m * n :=
begin
  rw finite_cardinals_iff_nat at hm hn, revert n, apply induction,
    rw [card_mul_empty (nat_is_cardinal hm), mul_base hm],
  intros k hk hi,
  have hm' : m.finite_cardinal, rw finite_cardinals_iff_nat, exact hm,
  have hk' : k.finite_cardinal, rw finite_cardinals_iff_nat, exact hk,
  nth_rewrite 0 ←card_add_one_eq_succ hk',
  rw [T6J_m2 (nat_is_cardinal hm) (nat_is_cardinal hk), hi],
  have hmk : (m * k).finite_cardinal, rw finite_cardinals_iff_nat, exact mul_into_nat hm hk,
  rw [card_add_eq_ord_add hmk hm', mul_ind hm hk],
end

theorem card_exp_eq_ord_exp {m : Set} (hm : m.finite_cardinal) {n : Set} (hn : n.finite_cardinal) : m.card_exp n = m ^ n :=
begin
  rw finite_cardinals_iff_nat at hm hn, revert n, apply induction,
    rw [card_exp_empty (nat_is_cardinal hm), exp_base hm],
  intros k hk hi,
  have hm' : m.finite_cardinal, rw finite_cardinals_iff_nat, exact hm,
  have hk' : k.finite_cardinal, rw finite_cardinals_iff_nat, exact hk,
  nth_rewrite 0 ←card_add_one_eq_succ hk',
  rw [T6J_e2 (nat_is_cardinal hm) (nat_is_cardinal hk), hi],
  have hmk : (m ^ k).finite_cardinal, rw finite_cardinals_iff_nat, exact exp_into_nat hm hk,
  rw [card_mul_eq_ord_mul hmk hm', exp_ind hm hk],
end

-- Corollary 6K
theorem union_finite_of_finite {A : Set} (hA : A.is_finite) {B : Set} (hB : B.is_finite) : (A ∪ B).is_finite :=
begin
  rw union_eq_union_diff,
  have hB' : (B \ A).is_finite := subset_finite_of_finite hB subset_diff,
  have hdisj : A ∩ (B \ A) = ∅ := self_inter_diff_empty,
  rw finite_iff at *, rcases hA with ⟨n, hn, hA⟩, rcases hB' with ⟨m, hm, hB'⟩, refine ⟨n + m, add_into_nat hn hm, _⟩,
  rw card_add_spec hA hB' hdisj, apply card_add_eq_ord_add,
    rw finite_cardinals_iff_nat, exact hn,
  rw finite_cardinals_iff_nat, exact hm,
end

theorem prod_finite_of_finite {A : Set} (hA : A.is_finite) {B : Set} (hB : B.is_finite) : (A.prod B).is_finite :=
begin
  rw finite_iff at *, rcases hA with ⟨n, hn, hA⟩, rcases hB with ⟨m, hm, hB⟩, refine ⟨n * m, mul_into_nat hn hm, _⟩,
  rw card_mul_spec hA hB, apply card_mul_eq_ord_mul,
    rw finite_cardinals_iff_nat, exact hn,
  rw finite_cardinals_iff_nat, exact hm,
end

theorem into_funs_finite_of_finite {A : Set} (hA : A.is_finite) {B : Set} (hB : B.is_finite) : (B.into_funs A).is_finite :=
begin
  rw finite_iff at *, rcases hA with ⟨n, hn, hA⟩, rcases hB with ⟨m, hm, hB⟩, refine ⟨n ^ m, exp_into_nat hn hm, _⟩,
  rw card_exp_spec hA hB, apply card_exp_eq_ord_exp,
    rw finite_cardinals_iff_nat, exact hn,
  rw finite_cardinals_iff_nat, exact hm,
end

def dominated (A B : Set) : Prop := ∃ f : Set, f.into_fun A B ∧ f.one_to_one
infix ≼ := dominated
lemma dominates_self {A : Set} : A ≼ A := ⟨A.id, id_into, id_oto⟩
lemma dominated_sub {A B : Set} (h : A ⊆ B) : A ≼ B := ⟨A.id, into_of_into_ran_sub h id_into, id_oto⟩
lemma dominated_iff {A B : Set} : A ≼ B ↔ ∃ C : Set, C ⊆ B ∧ A.equinumerous C :=
begin
  split,
  { rintro ⟨f, finto, foto⟩, exact ⟨_, finto.right.right, _, onto_ran_of_into finto, foto⟩, },
  { rintro ⟨C, hCB, f, fonto, foto⟩, exact ⟨_, into_of_onto_ran_sub hCB fonto, foto⟩, },
end

lemma dominated_of_equin_of_dominated {K₁ K₂ : Set} (hK : K₂.equinumerous K₁) {L₁ L₂ : Set} (hL : L₁.equinumerous L₂) (h : K₁ ≼ L₁) : (K₂ ≼ L₂) :=
begin
  rcases hK with ⟨F, Fonto, Foto⟩, rcases hL with ⟨G, Gonto, Goto⟩, rcases h with ⟨D, Dinto, Doto⟩,
  let H : Set := G.comp (D.comp F),
  exact ⟨H, comp_into_fun (comp_into_fun (into_of_onto Fonto) Dinto) (into_of_onto Gonto),
    comp_one_to_one Goto (comp_one_to_one Doto Foto)⟩,
end

lemma dominated_iff_equin {K₁ K₂ : Set} (hK : K₁.equinumerous K₂) {L₁ L₂ : Set} (hL : L₁.equinumerous L₂) : K₁ ≼ L₁ ↔ K₂ ≼ L₂ :=
⟨λ h, dominated_of_equin_of_dominated (equin_symm hK) hL h, λ h, dominated_of_equin_of_dominated hK (equin_symm hL) h⟩

def card_le (κ μ : Set) : Prop := ∀ ⦃K : Set⦄, K.card = κ → ∀ ⦃M : Set⦄, M.card = μ → K ≼ M

lemma card_le_iff_equin {κ K : Set} (hK : K.card = κ) {μ M : Set} (hM : M.card = μ) : κ.card_le μ ↔ K ≼ M :=
begin
  split,
  { intro h, exact h hK hM, },
  { intros h K' hK' M' hM', apply dominated_of_equin_of_dominated _ _ h,
      rw [←card_equiv, hK, hK'],
    rw [←card_equiv, hM, hM'], },
end

lemma card_le_iff_equin' {K L : Set} : K.card.card_le L.card ↔ K ≼ L :=
⟨λ h, (card_le_iff_equin rfl rfl).mp h, λ h, (card_le_iff_equin rfl rfl).mpr h⟩

def card_lt (κ μ : Set) : Prop := κ.card_le μ ∧ κ ≠ μ

lemma card_lt_iff {K L : Set} : K.card.card_lt L.card ↔ K ≼ L ∧ K ≉ L :=
by simp only [card_lt, card_le_iff_equin', ←card_equiv]

lemma card_le_iff {κ μ : Set} : κ.card_le μ ↔ κ.card_lt μ ∨ κ = μ :=
begin
  let P : Prop := κ = μ,
  rw [card_lt, and_or_distrib_right, or_comm (¬ P) _, (iff_true (P ∨ ¬P)).mpr (classical.em P), and_true], split,
    intro h, exact or.inl h,
  rintro (h|h),
    exact h,
  intros K hK M hM, rw [←hK, ←hM] at h, rw dominated_iff, use M, refine ⟨subset_self, _⟩,
  rw ←card_equiv, exact h,
end

lemma card_le_of_subset {A B : Set} (hAB : A ⊆ B) : A.card.card_le B.card :=
begin
  rw card_le_iff_equin rfl rfl, exact ⟨A.id, into_of_into_ran_sub hAB id_into, id_oto⟩,
end

lemma exists_sets_of_card_le {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) (h : κ.card_le μ) :
∃ K M : Set, K ⊆ M ∧ K.card = κ ∧ M.card = μ :=
begin
  rcases hκ with ⟨K, hK⟩, rcases hμ with ⟨M, hM⟩,
  have hd : K ≼ M, rw [←card_le_iff_equin rfl rfl, hK, hM], exact h,
  rcases hd with ⟨f, finto, foto⟩,
  refine ⟨f.ran, M, finto.right.right, _, hM⟩,
  rw [←hK, card_equiv], apply equin_symm, exact ⟨f, ⟨finto.left, finto.right.left, rfl⟩, foto⟩,
end

lemma zero_card_le {κ : Set} (hκ : κ.is_cardinal) : card_le ∅ κ :=
begin
  rcases hκ with ⟨K, hK⟩, rw [←hK, ←card_nat zero_nat], apply card_le_of_subset,
  intros z hz, exfalso, exact mem_empty _ hz,
end

lemma finite_card_lt_aleph_null {n : Set} (hn : n.finite_cardinal) : n.card_lt ℵ₀ :=
begin
  rw finite_cardinals_iff_nat at hn, rw [←card_nat hn, card_lt], split,
    apply card_le_of_subset, exact subset_nat_of_mem_nat hn,
  intro h, apply nat_infinite, rw card_equiv at h, exact ⟨_, hn, equin_symm h⟩,
end

lemma finite_card_le_iff_le {n : Set} (hn : n.finite_cardinal) {m : Set} (hm : m.finite_cardinal) : m.card_le n ↔ m ≤ n :=
begin
  split,
  { intro h,
    rw finite_cardinals_iff_nat at hn hm,
    rw [←card_nat hm, ←card_nat hn, card_le_iff_equin'] at h,
    apply le_of_not_lt hn hm, intro hnm, rw ←nat_ssub_iff_mem hn hm at hnm,
    rcases h with ⟨f, finto, foto⟩,
    exact pigeonhole'' (ssub_of_sub_of_ssub finto.right.right hnm) ⟨f, onto_ran_of_into finto, foto⟩ (nat_finite hm), },
  { intro h,
    rw finite_cardinals_iff_nat at hn hm,
    rw ←nat_sub_iff_le hm hn at h,
    rw [←card_nat hm, ←card_nat hn],
    exact card_le_of_subset h, },
end

lemma card_lt_exp {κ : Set} (hκ : κ.is_cardinal) : card_lt κ (card_exp two κ) :=
begin
  rcases hκ with ⟨K, hK⟩, rw [←hK, ←card_power, card_lt_iff], split,
    let f := pair_sep_eq K K.powerset (λ x, {x}),
    have finto : f.into_fun K K.powerset, apply pair_sep_eq_into, intros x hx,
      simp only [mem_powerset], intros z hz, rw mem_singleton at hz, rw hz, exact hx,
    have foto : f.one_to_one, apply pair_sep_eq_oto, intros x hx x' hx' he,
      rw ←ext_iff at he, simp only [mem_singleton] at he, specialize he x, rw ←he,
    exact ⟨f, finto, foto⟩,
  exact not_equin_powerset,
    
end

lemma card_le_refl {κ : Set} : κ.card_le κ :=
begin
  intros K hK M hM, rw [←hM, card_equiv] at hK, rw dominated_iff, exact ⟨_, subset_self, hK⟩,
end

lemma card_le_trans {κ μ : Set} (hμ : μ.is_cardinal) (hκμ : κ.card_le μ) {ν : Set} (hμν : μ.card_le ν) : κ.card_le ν :=
begin
  rcases hμ with ⟨M, hM⟩, intros K hK N hN, specialize hκμ hK hM, specialize hμν hM hN,
  rcases hκμ with ⟨f, finto, foto⟩, rcases hμν with ⟨g, ginto, goto⟩,
  exact ⟨g.comp f, comp_into_fun finto ginto, comp_one_to_one goto foto⟩,
end

-- Schröer-Bernstein Theorem part a
lemma equin_of_dom_of_dom {A B : Set} (hAB : A ≼ B) (hBA : B ≼ A) : A ≈ B :=
begin
  rcases hAB with ⟨f, finto, foto⟩, rcases hBA with ⟨g, ginto, goto⟩,
  let C : ℕ → Set := @nat.rec (λ n, Set) (A \ g.ran) (λ _ C, g.img (f.img C)),
  have hnz : ∀ {x}, x ∈ A → ¬ (∃ n, x ∈ C n) → x ∈ g.ran, intros x hx hc,
    have hnz : x ∉ A \ g.ran, intro hz, exact hc ⟨0, hz⟩,
    rw [mem_diff] at hnz, apply by_contradiction, intro hngr, exact hnz ⟨hx, hngr⟩,
  have Csub : ∀ {n}, C n ⊆ A, intro n, induction n with n ih,
    { exact subset_diff, },
    { exact subset_trans img_subset_ran ginto.right.right, },
  let h' : Set → Set := (λ x, if ∃ n, x ∈ C n then f.fun_value x else g.inv.fun_value x),
  let h := pair_sep_eq A B h',
  have hfun := pair_sep_eq_is_fun,
  have hdom : h.dom = A, apply pair_sep_eq_dom_eq, intros x hx,
    by_cases hc : ∃ n, x ∈ C n,
    { dsimp [h'], simp only [hc, if_true], apply finto.right.right, apply fun_value_def'' finto.left,
      rw finto.right.left, exact hx, },
    { dsimp [h'], simp only [hc, if_false, ←ginto.right.left, ←T3E_b],
      apply fun_value_def'',
        rw T3F_a, exact goto,
      rw T3E_a, exact hnz hx hc, },
  have hoto : h.one_to_one, apply pair_sep_eq_oto,
    have hb : ∀ {x}, x ∈ A → (∃ n, x ∈ C n) → ∀ {x'}, x' ∈ A → (¬ ∃ n, x' ∈ C n) → h' x = h' x' → x = x',
      intros x hx hc x' hx' hc' he,
      dsimp [h'] at he, simp only [hc, hc', if_true, if_false] at he,
      rcases hc with ⟨n, hc⟩,
      have hf : f.fun_value x ∈ f.img (C n), refine fun_value_mem_img finto.left _ hc,
        rw finto.right.left, exact Csub,
      rw he at hf, rw mem_img' finto.left at hf, rcases hf with ⟨x'', hc'', he'⟩,
      have he'' : g.fun_value (g.inv.fun_value x') = g.fun_value (f.fun_value x''), rw he',
      rw ←T3H_c ginto.left (T3F_a.mpr goto) at he'', rw eq_inv_id  ginto.left goto at he'',
      rw id_value (hnz hx' hc') at he'', exfalso, apply hc', use n.succ,
      have h' : f.img (C n) ⊆ g.dom, rw ginto.right.left, exact subset_trans img_subset_ran finto.right.right,
      have h'' : C n ⊆ f.dom, rw finto.right.left, exact Csub,
      simp only [mem_img' ginto.left h', mem_img' finto.left h''],
      refine ⟨f.fun_value x'', ⟨_, hc'', rfl⟩, he''⟩,
      have h''' : g.inv.ran ⊆ g.dom, rw [T3E_b, ginto.right.left], exact subset_self,
      rw [dom_comp h''', T3E_a], exact hnz hx' hc',
      rw finto.right.left, exact Csub,
    intros x hx x' hx' he,
    by_cases hc : (∃ n, x ∈ C n);
    by_cases hc' : ∃ n, x' ∈ C n,
    { dsimp [h'] at he, simp only [hc, hc', if_true] at he, rw [←finto.right.left] at hx hx',
      exact from_one_to_one finto.left foto hx hx' he, },
    { exact hb hx hc hx' hc' he, },
    { symmetry, exact hb hx' hc' hx hc he.symm, },
    { dsimp [h'] at he, simp only [hc, hc', if_false] at he,
      apply from_one_to_one (T3F_a.mpr goto) ((T3F_b ginto.left.left).mp ginto.left),
        rw T3E_a, exact hnz hx hc,
      rw T3E_a, exact hnz hx' hc',
      exact he, },
  have hran : h.ran = B, apply pair_sep_eq_ran_eq, intros y hy,
    by_cases hc : ∃ n, y ∈ f.img (C n),
    { rcases hc with ⟨n, hc⟩,
      have Csub' : C n ⊆ f.dom, rw finto.right.left, exact Csub,
      simp only [mem_img' finto.left Csub'] at hc,
      rcases hc with ⟨x, hx, hc⟩, refine ⟨x, Csub hx, _⟩,
      dsimp [h'], simp only [exists.intro n hx, if_true], exact hc, },
    { refine ⟨g.fun_value y, _, _⟩,
        apply ginto.right.right, apply fun_value_def'' ginto.left, rw ginto.right.left, exact hy,
      have hne : ¬ ∃ n, g.fun_value y ∈ C n, rintro ⟨n, hn⟩,
        cases n with n,
          rw mem_diff at hn, apply hn.right, apply fun_value_def'' ginto.left, rw ginto.right.left, exact hy,
        have hfimg : f.img (C n) ⊆ g.dom, rw ginto.right.left, exact subset_trans img_subset_ran finto.right.right,
        rw mem_img' ginto.left hfimg at hn, rcases hn with ⟨y', hy', he⟩, apply hc, use n,
        suffices he' : y = y',
          rw he', exact hy',
        refine from_one_to_one ginto.left goto _ _ he,
          rw ginto.right.left, exact hy,
        rw ginto.right.left, exact (subset_trans img_subset_ran finto.right.right) hy',
      dsimp [h'], simp only [hne, if_false],
      rw [←T3H_c (T3F_a.mpr goto) ginto.left, eq_id ginto.left goto, ginto.right.left, id_value hy],
      rw [dom_comp, ginto.right.left], exact hy,
      rw T3E_a, exact subset_self, },
  exact ⟨_, ⟨hfun, hdom, hran⟩, hoto⟩,
end

-- Schröer-Bernstein Theorem part b
lemma card_eq_of_le_of_le {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) (hκμ : κ.card_le μ) (hμκ : μ.card_le κ) : κ = μ :=
begin
  rcases hκ with ⟨K, hK⟩, rcases hμ with ⟨M, hM⟩, rw [←hK, ←hM, card_equiv],
  apply equin_of_dom_of_dom (hκμ hK hM) (hμκ hM hK),
end

-- Too lazy to do theorem 6L

-- excercise  15
theorem not_exists_dominators : ¬ ∃ K : Set, ∀ A : Set, ∃ B : Set, B ∈ K ∧ A ≼ B :=
begin
  rintro ⟨K, h⟩, apply @not_equin_powerset K.Union, apply equin_of_dom_of_dom,
    rw dominated_iff_equin equin_refl powerset_equinumerous_into_funs,
    rw ←card_le_iff_equin', rw card_exp_spec rfl rfl, rw card_le_iff, left,
    rw card_nat two_nat, exact card_lt_exp ⟨_, rfl⟩,
  specialize h K.Union.powerset, rcases h with ⟨B, hBK, hB⟩,
  rw ←card_le_iff_equin', rw ←card_le_iff_equin' at hB,
  refine card_le_trans ⟨_, rfl⟩ hB _,
  rw card_le_iff_equin',
  exact dominated_sub (subset_Union_of_mem hBK),
end


def is_chain (B : Set) : Prop := ∀ ⦃C : Set⦄, C ∈ B → ∀ ⦃D : Set⦄, D ∈ B → C ⊆ D ∨ D ⊆ C

-- some of these to be proved at end of chapter 7
def Axiom_of_choice_V : Prop := ∀ C D : Set, C ≼ D ∨ D ≼ C
def Axiom_of_choice_VI : Prop := ∀ 𝓐 : Set, (∀ 𝓑 : Set, 𝓑.is_chain → 𝓑 ⊆ 𝓐 → 𝓑.Union ∈ 𝓐) → ∃ M, M ∈ 𝓐 ∧ ∀ N ∈ 𝓐, N ≠ M → ¬(M ⊆ N)

lemma choice_equiv_6_1 : Axiom_of_choice_VI.{u} → Axiom_of_choice_I.{u} :=
begin
  dsimp [Axiom_of_choice_VI, Axiom_of_choice_I], intros ax6 R hR,
  let 𝓐 : Set := {f ∈ R.powerset | f.is_function},
  have huncl : ∀ 𝓑 : Set, 𝓑.is_chain → 𝓑 ⊆ 𝓐 → 𝓑.Union ∈ 𝓐,
    intros 𝓑 hch h𝓑𝓐, simp only [mem_sep, mem_powerset], split,
      apply Union_subset_of_subset_powerset, intros B hB,
      have h : B ∈ 𝓐 := h𝓑𝓐 hB,
      rw Set.mem_sep at h, exact h.left,
    rw is_function_iff, split,
      intros b hb, rw mem_Union at hb, rcases hb with ⟨B, hB𝓑, hbB⟩, specialize h𝓑𝓐 hB𝓑,
      rw Set.mem_sep at h𝓑𝓐, replace h𝓑𝓐 := h𝓑𝓐.right.left, exact h𝓑𝓐 _ hbB,
    intros x y y' hxy hxy', simp only [mem_Union, exists_prop] at hxy hxy',
    rcases hxy with ⟨Z, hZ𝓑, hxyZ⟩, rcases hxy' with ⟨Z', hZ𝓑', hxyZ'⟩,
    specialize hch hZ𝓑 hZ𝓑', cases hch,
      have hZ𝓐' : Z' ∈ 𝓐 := h𝓑𝓐 hZ𝓑',
      rw [mem_sep, is_function_iff] at hZ𝓐',
      apply hZ𝓐'.right.right _ _ _ (hch hxyZ) hxyZ',
    have hZ𝓐 : Z ∈ 𝓐 := h𝓑𝓐 hZ𝓑,
    rw [mem_sep, is_function_iff] at hZ𝓐,
    apply hZ𝓐.right.right _ _ _ hxyZ (hch hxyZ'),
  specialize ax6 _ huncl, rcases ax6 with ⟨F, hf𝓐, hmax⟩, rw [mem_sep, mem_powerset] at hf𝓐,
  refine ⟨_, hf𝓐.right, hf𝓐.left, _⟩, apply ext, intros x, split,
    intro hx, rw mem_dom at *, rcases hx with ⟨y, hxy⟩, exact ⟨_, hf𝓐.left hxy⟩,
  intro hx, apply classical.by_contradiction, intro hnx, rw mem_dom at hx, rcases hx with ⟨y, hxy⟩,
  let F' := F ∪ {x.pair y},
  apply hmax F',
      rw [mem_sep, mem_powerset], split,
        apply union_subset_of_subset_of_subset hf𝓐.left,
        intros z hz, rw mem_singleton at hz, subst hz, exact hxy,
      apply union_singleton_is_fun hf𝓐.right hnx,
    intros he,
    have hxyF' : x.pair y ∈ F', rw [mem_union, mem_singleton], right, refl,
    rw he at hxyF', apply hnx, rw mem_dom, exact ⟨_, hxyF'⟩,
  exact subset_union_left,
end

lemma choice_equiv_6_5 : Axiom_of_choice_VI.{u} → Axiom_of_choice_V.{u} :=
begin
  dsimp [Axiom_of_choice_VI, Axiom_of_choice_V], intros ax6 C D, sorry,
end

end Set