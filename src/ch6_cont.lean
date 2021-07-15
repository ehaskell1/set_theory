import ch7
universe u
namespace Set

local attribute [irreducible] mem

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

lemma card_finite_iff_finite {A : Set} : A.card.finite_cardinal ↔ A.is_finite :=
⟨λ h, one_finite_all_finite h rfl, λ h, ⟨_, h, rfl⟩⟩

theorem finite_cardinal_iff_nat {X : Set} : X.finite_cardinal ↔ X ∈ ω :=
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
          rw [mem_succ_iff_le, le_iff] at hxk, cases hxk,
          { left, exact ⟨hxC, hxk⟩, },
          { right, exact hxk, }, },
        { rintro (⟨hxC, hxk⟩|hxk),
          { exact hxC, },
          { rw ←hxk at hkmC, exact hkmC, }, },
        have hCkp : C ∩ k ⊂ k, refine ⟨λ x hx, _, _⟩,
          { rw mem_inter at hx, exact hx.right, },
          { intro hCke, apply hCk.right, rw eq_iff_subset_and_subset, refine ⟨hCk.left, λ x hxk, _⟩,
            rw [mem_succ_iff_le, le_iff] at hxk, cases hxk,
            { rw ←hCke at hxk, rw mem_inter at hxk, exact hxk.left, },
            { rw ←hxk at hkmC, exact hkmC, }, },
        specialize hi hCkp, rcases hi with ⟨m, hmk, f, fonto, foto⟩,
        let g : Set := f ∪ {k.pair m},
        have ginto : g.into_fun C m.succ, rw fun_def_equiv,
          have hf : (C ∩ k).is_func m f, rw ←fun_def_equiv, exact into_of_onto fonto,
          refine ⟨λ p hp, _, λ x hxC, _⟩,
          { simp only [mem_prod, exists_prop, mem_succ_iff_le, le_iff], rw [mem_union, mem_singleton] at hp,
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
          rw [mem_succ_iff_le, le_iff] at hxk, cases hxk,
          { exact hxk, },
          { exfalso, rw hxk at hxC, exact hkmC hxC, },
        specialize hi hCpk, rcases hi with ⟨m, hmk, hCm⟩,
        simp only [mem_succ_iff_le, le_iff], exact ⟨_, or.inl hmk, hCm⟩, }, }, },
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

lemma inf_of_sup_inf {X : Set} (Xinf : ¬ X.is_finite) {Y : Set} (XY : X ⊆ Y) : ¬ Y.is_finite :=
λ Yfin, Xinf (subset_finite_of_finite Yfin XY)

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

lemma add_cardinal {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) : (κ.card_add μ).is_cardinal :=
begin
  rcases hκ with ⟨K, hK⟩, rcases hμ with ⟨M, hM⟩,
  let K' := K.prod {∅},
  let M' := M.prod {one},
  have hK' : K'.card = κ, rw same_card, exact hK,
  have hM' : M'.card = μ, rw same_card, exact hM,
  have hdisj : K' ∩ M' = ∅ := disj zero_ne_one,
  rw ←card_add_spec hK' hM' hdisj, exact ⟨_, rfl⟩,
end

lemma mul_cardinal {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) : (κ.card_mul μ).is_cardinal :=
begin
  rcases hκ with ⟨K, hK⟩, rcases hμ with ⟨M, hM⟩,
  rw ←card_mul_spec hK hM, exact ⟨_, rfl⟩,
end

lemma exp_cardinal {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) : (κ.card_exp μ).is_cardinal :=
begin
  rcases hκ with ⟨K, hK⟩, rcases hμ with ⟨M, hM⟩,
  rw ←card_exp_spec hK hM, exact ⟨_, rfl⟩,
end

theorem aleph_mul_aleph_eq_aleph : card_mul ℵ₀ ℵ₀ = ℵ₀ :=
begin
  rw [←card_mul_spec rfl rfl, card_equiv], exact nat_prod_nat_equin_nat,
end

-- example 4, part c, page 141
theorem card_mul_one_eq_self {κ : Set} (hκ : κ.is_cardinal) : κ.card_mul one = κ :=
begin
  rcases hκ with ⟨K, hK⟩, rw [←card_mul_spec hK (card_nat one_nat), ←hK, card_equiv, one, succ, union_empty],
  apply equin_symm, exact prod_singleton_equin,
end

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

-- Theorem 6I part 1 part b
theorem card_mul_comm {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) : κ.card_mul μ = μ.card_mul κ :=
begin
  rcases hκ with ⟨K, hK⟩,
  rcases hμ with ⟨M, hM⟩,
  rw [←card_mul_spec hK hM, ←card_mul_spec hM hK, card_equiv],
  let f : Set := pair_sep_eq (K.prod M) (M.prod K) (λ z, z.snd.pair z.fst),
  refine ⟨f, ⟨pair_sep_eq_is_fun, pair_sep_eq_dom_eq _, pair_sep_eq_ran_eq _⟩, pair_sep_eq_oto _⟩,
  { intros z hz, rw mem_prod at hz, rcases hz with ⟨k, hk, m, hm, he⟩, subst he,
    rw [pair_mem_prod, snd_congr, fst_congr], exact ⟨hm, hk⟩, },
  { intros z hz, rw mem_prod at hz, rcases hz with ⟨m, hm, k, hk, he⟩, subst he, use k.pair m,
    simp only [pair_mem_prod, snd_congr, fst_congr],
    exact ⟨⟨hk, hm⟩, rfl⟩, },
  { intros z hz z' hz' he,
    obtain ⟨snde, fste⟩ := pair_inj he,
    rw mem_prod at hz, rw mem_prod at hz',
    rcases hz with ⟨k, hk, m, hm, hze⟩, rcases hz' with ⟨k', hk', m', hm', hze'⟩,
    subst hze, subst hze', simp only [snd_congr] at snde, simp only [fst_congr] at fste,
    subst snde, subst fste, },
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

-- theorem 6I part 6
theorem card_exp_exp {κ : Set.{u}} (hκ : κ.is_cardinal) {μ : Set.{u}} (hμ : μ.is_cardinal) {ν : Set.{u}} (hν : ν.is_cardinal) :
(κ.card_exp μ).card_exp ν = κ.card_exp (μ.card_mul ν) :=
begin
  rcases hκ with ⟨K, hK⟩,
  rcases hμ with ⟨M, hM⟩,
  rcases hν with ⟨N, hN⟩,
  rw [←card_exp_spec hK hM, ←card_exp_spec rfl hN, ←card_mul_spec hM hN, ←card_exp_spec hK rfl, card_equiv],
  let H : Set.{u} := pair_sep_eq (N.into_funs (M.into_funs K)) ((M.prod N).into_funs K) (λ f, pair_sep_eq (M.prod N) K (λ z, (f.fun_value z.snd).fun_value z.fst)),
  refine ⟨H, ⟨pair_sep_eq_is_fun, pair_sep_eq_dom_eq _, pair_sep_eq_ran_eq _⟩, pair_sep_eq_oto _⟩,
  { intros f hf, rw mem_into_funs at *, dsimp, apply pair_sep_eq_into, intros z hz, rw mem_prod at hz,
    rcases hz with ⟨m, hm, n, hn, he⟩, subst he, rw [fst_congr, snd_congr],
    have hfn : (f.fun_value n).into_fun M K, rw ←mem_into_funs, apply hf.right.right,
      apply fun_value_def'' hf.left, rw hf.right.left, exact hn,
    apply hfn.right.right, apply fun_value_def'' hfn.left, rw hfn.right.left, exact hm, },
  { intros f hf, dsimp,
    use pair_sep_eq N (M.into_funs K) (λ n, pair_sep_eq M K (λ m, f.fun_value (m.pair n))), split,
    { rw mem_into_funs, apply pair_sep_eq_into, intros n hn, rw mem_into_funs, apply pair_sep_eq_into,
      intros m hm, rw mem_into_funs at hf, apply hf.right.right, apply fun_value_def'' hf.left,
      rw [hf.right.left, pair_mem_prod], exact ⟨hm, hn⟩, },
    { rw mem_into_funs at hf, apply fun_ext hf.left pair_sep_eq_is_fun,
      { rw hf.right.left, symmetry, apply pair_sep_eq_dom_eq, intros z hz, rw mem_prod at hz, dsimp,
        obtain ⟨a, aM, b, bN, zab⟩ := hz, subst zab, simp only [fst_congr, snd_congr],
        have dom : (N.pair_sep_eq (M.into_funs K) (λ (n : Set), M.pair_sep_eq K (λ (m : Set), f.fun_value (m.pair n)))).dom = N,
          apply pair_sep_eq_dom_eq, intros n nN, rw mem_into_funs, dsimp, apply pair_sep_eq_into,
          intros m mM, apply hf.right.right, apply fun_value_def'' hf.left, rw [hf.right.left, pair_mem_prod],
          exact ⟨mM, nN⟩,
        rw ←dom at bN, rw pair_sep_eq_fun_value bN, dsimp,
        have dom' : (M.pair_sep_eq K (λ (m : Set), f.fun_value (m.pair b))).dom = M,
          apply pair_sep_eq_dom_eq, intros m mM, dsimp, apply hf.right.right, apply fun_value_def'' hf.left,
          rw [hf.right.left, pair_mem_prod], rw dom at bN, exact ⟨mM, bN⟩,
        rw ←dom' at aM, rw pair_sep_eq_fun_value aM, dsimp, apply hf.right.right, apply fun_value_def'' hf.left,
        rw [hf.right.left, pair_mem_prod], rw dom at bN, rw dom' at aM, exact ⟨aM, bN⟩, },
      { intros z hz,
        have hz' : z ∈ (pair_sep_eq (M.prod N) K (λ (z : Set),
          ((N.pair_sep_eq (M.into_funs K)
              (λ (n : Set), M.pair_sep_eq K (λ (m : Set), f.fun_value (m.pair n)))).fun_value
             z.snd).fun_value
            z.fst)).dom,
          have hd : (pair_sep_eq (M.prod N) K (λ (z : Set),
          ((N.pair_sep_eq (M.into_funs K)
              (λ (n : Set), M.pair_sep_eq K (λ (m : Set), f.fun_value (m.pair n)))).fun_value
             z.snd).fun_value
            z.fst)).dom = (M.prod N),
            apply pair_sep_eq_dom_eq, intros z hz, rw mem_prod at hz, dsimp,
            obtain ⟨a, aM, b, bN, zab⟩ := hz, subst zab, simp only [snd_congr, fst_congr],
            have dom : (N.pair_sep_eq (M.into_funs K) (λ (n : Set), M.pair_sep_eq K (λ (m : Set), f.fun_value (m.pair n)))).dom = N,
              apply pair_sep_eq_dom_eq, intros n nN, rw mem_into_funs, dsimp, apply pair_sep_eq_into,
              intros m mM, apply hf.right.right, apply fun_value_def'' hf.left, rw [hf.right.left, pair_mem_prod],
              exact ⟨mM, nN⟩,
            rw ←dom at bN, rw pair_sep_eq_fun_value bN, dsimp,
            have dom' : (M.pair_sep_eq K (λ (m : Set), f.fun_value (m.pair b))).dom = M,
              apply pair_sep_eq_dom_eq, intros m mM, dsimp, apply hf.right.right, apply fun_value_def'' hf.left,
              rw [hf.right.left, pair_mem_prod], rw dom at bN, exact ⟨mM, bN⟩,
            rw ←dom' at aM, rw pair_sep_eq_fun_value aM, dsimp, apply hf.right.right, apply fun_value_def'' hf.left,
            rw [hf.right.left, pair_mem_prod], rw dom at bN, rw dom' at aM, exact ⟨aM, bN⟩,
          rw hd, rw hf.right.left at hz, exact hz,
        change f.fun_value z = (pair_sep_eq (M.prod N) K (λ (z : Set),
          ((N.pair_sep_eq (M.into_funs K)
              (λ (n : Set), M.pair_sep_eq K (λ (m : Set), f.fun_value (m.pair n)))).fun_value
             z.snd).fun_value
            z.fst)).fun_value z,
        rw pair_sep_eq_fun_value hz', rw [hf.right.left, mem_prod] at hz, rcases hz with ⟨m, hm, n, hn, he⟩, subst he,
        dsimp, rw [fst_congr, snd_congr],
        have hfn : n ∈ (pair_sep_eq N (M.into_funs K) (λ (n : Set), M.pair_sep_eq K (λ (m : Set), f.fun_value (m.pair n)))).dom,
          have hd : (pair_sep_eq N (M.into_funs K) (λ (n : Set), M.pair_sep_eq K (λ (m : Set), f.fun_value (m.pair n)))).dom = N,
            apply pair_sep_eq_dom_eq, intros n' hn', rw mem_into_funs, apply pair_sep_eq_into,
            intros m' hm', apply hf.right.right, apply fun_value_def'' hf.left, rw [hf.right.left, pair_mem_prod], exact ⟨hm', hn'⟩,
          rw hd, exact hn,
        rw pair_sep_eq_fun_value hfn, dsimp,
        have hfm : m ∈ (pair_sep_eq M K (λ (m : Set), f.fun_value (m.pair n))).dom,
          have hd : (pair_sep_eq M K (λ (m : Set), f.fun_value (m.pair n))).dom = M,
            apply pair_sep_eq_dom_eq, intros m' hm', dsimp, apply hf.right.right, apply fun_value_def'' hf.left,
            rw [hf.right.left, pair_mem_prod], exact ⟨hm', hn⟩,
          rw hd, exact hm,
        rw pair_sep_eq_fun_value hfm, }, }, },
  { simp only [mem_into_funs], intros f hf g hg he, apply fun_ext hf.left hg.left,
    { rw [hf.right.left, hg.right.left], },
    { intros n hn,
      have hf' : (f.fun_value n).into_fun M K, rw ←mem_into_funs, exact hf.right.right (fun_value_def'' hf.left hn),
      have hg' : (g.fun_value n).into_fun M K, rw ←mem_into_funs, refine hg.right.right (fun_value_def'' hg.left _),
        rw [hg.right.left, ←hf.right.left], exact hn,
      apply fun_ext hf'.left hg'.left,
        rw [hf'.right.left, hg'.right.left],
      intros m hm,
      have hf'' : (pair_sep_eq (M.prod N) K (λ (z : Set), (f.fun_value z.snd).fun_value z.fst)).fun_value (m.pair n)
        = (f.fun_value (m.pair n).snd).fun_value (m.pair n).fst,
        apply pair_sep_eq_fun_value,
        have hd : (pair_sep_eq (M.prod N) K (λ (z : Set), (f.fun_value z.snd).fun_value z.fst)).dom = (M.prod N),
          apply pair_sep_eq_dom_eq, intros z hz, dsimp, rw mem_prod at hz, rcases hz with ⟨m, hm, n', hn', he⟩, subst he,
          rw [fst_congr, snd_congr],
          have hfn' : (f.fun_value n').into_fun M K, rw ←mem_into_funs, refine hf.right.right (fun_value_def'' hf.left _),
            rw hf.right.left, exact hn',
          apply hfn'.right.right, apply fun_value_def'' hfn'.left, rw hfn'.right.left, exact hm,
        rw [hd, pair_mem_prod], rw hf.right.left at hn, rw hf'.right.left at hm, exact ⟨hm, hn⟩,
      have hg'' : (pair_sep_eq (M.prod N) K (λ (z : Set), (g.fun_value z.snd).fun_value z.fst)).fun_value (m.pair n)
        = (g.fun_value (m.pair n).snd).fun_value (m.pair n).fst,
        apply pair_sep_eq_fun_value,
        have hd : (pair_sep_eq (M.prod N) K (λ (z : Set), (g.fun_value z.snd).fun_value z.fst)).dom = (M.prod N),
          apply pair_sep_eq_dom_eq, intros z hz, dsimp, rw mem_prod at hz, rcases hz with ⟨m, hm, n', hn', he⟩, subst he,
          rw [fst_congr, snd_congr],
          have hgn' : (g.fun_value n').into_fun M K, rw ←mem_into_funs, refine hg.right.right (fun_value_def'' hg.left _),
            rw hg.right.left, exact hn',
          apply hgn'.right.right, apply fun_value_def'' hgn'.left, rw hgn'.right.left, exact hm,
        rw [hd, pair_mem_prod], rw hf.right.left at hn, rw hf'.right.left at hm, exact ⟨hm, hn⟩,
      rw [fst_congr, snd_congr] at hf'' hg'',
      rw [←hf'', ←hg'', he], }, },
end

theorem one_card_mul_eq_self {κ : Set} (hκ : κ.is_cardinal) : one.card_mul κ = κ :=
begin
  rw card_mul_comm (nat_is_cardinal one_nat) hκ, exact card_mul_one_eq_self hκ,
end

lemma card_add_empty {κ : Set} (hκ : κ.is_cardinal) : κ.card_add ∅ = κ :=
begin
  rcases hκ with ⟨K, hK⟩,
  rw ←card_add_spec hK (card_nat zero_nat) inter_empty, rw union_empty, exact hK,
end

lemma card_empty_add {κ : Set} (hκ : κ.is_cardinal) : card_add ∅ κ = κ :=
begin
  rw card_add_comm (nat_is_cardinal zero_nat) hκ, exact card_add_empty hκ,
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
  rw finite_cardinal_iff_nat at hm hn, revert n, apply induction,
    rw [card_add_empty (nat_is_cardinal hm), add_base hm],
  intros k hk hi,
  have hk' : k.finite_cardinal, rw finite_cardinal_iff_nat, exact hk,
  nth_rewrite 0 ←card_add_one_eq_succ hk',
  rw [T6J_a2 (nat_is_cardinal hm) (nat_is_cardinal hk), hi],
  have hmk : (m + k).finite_cardinal, rw finite_cardinal_iff_nat, exact add_into_nat hm hk,
  rw [card_add_one_eq_succ hmk, add_ind hm hk],
end

theorem card_mul_eq_ord_mul {m : Set} (hm : m.finite_cardinal) {n : Set} (hn : n.finite_cardinal) : m.card_mul n = m * n :=
begin
  rw finite_cardinal_iff_nat at hm hn, revert n, apply induction,
    rw [card_mul_empty (nat_is_cardinal hm), mul_base hm],
  intros k hk hi,
  have hm' : m.finite_cardinal, rw finite_cardinal_iff_nat, exact hm,
  have hk' : k.finite_cardinal, rw finite_cardinal_iff_nat, exact hk,
  nth_rewrite 0 ←card_add_one_eq_succ hk',
  rw [T6J_m2 (nat_is_cardinal hm) (nat_is_cardinal hk), hi],
  have hmk : (m * k).finite_cardinal, rw finite_cardinal_iff_nat, exact mul_into_nat hm hk,
  rw [card_add_eq_ord_add hmk hm', mul_ind hm hk],
end

theorem card_exp_eq_ord_exp {m : Set} (hm : m.finite_cardinal) {n : Set} (hn : n.finite_cardinal) : m.card_exp n = m ^ n :=
begin
  rw finite_cardinal_iff_nat at hm hn, revert n, apply induction,
    rw [card_exp_empty (nat_is_cardinal hm), exp_base hm],
  intros k hk hi,
  have hm' : m.finite_cardinal, rw finite_cardinal_iff_nat, exact hm,
  have hk' : k.finite_cardinal, rw finite_cardinal_iff_nat, exact hk,
  nth_rewrite 0 ←card_add_one_eq_succ hk',
  rw [T6J_e2 (nat_is_cardinal hm) (nat_is_cardinal hk), hi],
  have hmk : (m ^ k).finite_cardinal, rw finite_cardinal_iff_nat, exact exp_into_nat hm hk,
  rw [card_mul_eq_ord_mul hmk hm', exp_ind hm hk],
end

-- example 8, page 142
theorem card_add_self_eq_two_mul_self {κ : Set} (hκ : κ.is_cardinal) : κ.card_add κ = two.card_mul κ :=
begin
  rw [card_mul_comm (nat_is_cardinal two_nat) hκ, two, succ_eq_add_one one_nat],
  have one_fin : one.finite_cardinal, rw finite_cardinal_iff_nat, exact one_nat,
  rw [←card_add_eq_ord_add one_fin one_fin, card_mul_add hκ (nat_is_cardinal one_nat) (nat_is_cardinal one_nat)],
  rw [card_mul_one_eq_self hκ],
end

-- Corollary 6K
theorem union_finite_of_finite {A : Set} (hA : A.is_finite) {B : Set} (hB : B.is_finite) : (A ∪ B).is_finite :=
begin
  rw union_eq_union_diff,
  have hB' : (B \ A).is_finite := subset_finite_of_finite hB subset_diff,
  have hdisj : A ∩ (B \ A) = ∅ := self_inter_diff_empty,
  rw finite_iff at *, rcases hA with ⟨n, hn, hA⟩, rcases hB' with ⟨m, hm, hB'⟩, refine ⟨n + m, add_into_nat hn hm, _⟩,
  rw card_add_spec hA hB' hdisj, apply card_add_eq_ord_add,
    rw finite_cardinal_iff_nat, exact hn,
  rw finite_cardinal_iff_nat, exact hm,
end

theorem prod_finite_of_finite {A : Set} (hA : A.is_finite) {B : Set} (hB : B.is_finite) : (A.prod B).is_finite :=
begin
  rw finite_iff at *, rcases hA with ⟨n, hn, hA⟩, rcases hB with ⟨m, hm, hB⟩, refine ⟨n * m, mul_into_nat hn hm, _⟩,
  rw card_mul_spec hA hB, apply card_mul_eq_ord_mul,
    rw finite_cardinal_iff_nat, exact hn,
  rw finite_cardinal_iff_nat, exact hm,
end

theorem into_funs_finite_of_finite {A : Set} (hA : A.is_finite) {B : Set} (hB : B.is_finite) : (B.into_funs A).is_finite :=
begin
  rw finite_iff at *, rcases hA with ⟨n, hn, hA⟩, rcases hB with ⟨m, hm, hB⟩, refine ⟨n ^ m, exp_into_nat hn hm, _⟩,
  rw card_exp_spec hA hB, apply card_exp_eq_ord_exp,
    rw finite_cardinal_iff_nat, exact hn,
  rw finite_cardinal_iff_nat, exact hm,
end

lemma dominates_self {A : Set} : A ≼ A := ⟨A.id, id_into, id_oto⟩
lemma dominated_sub {A B : Set} (h : A ⊆ B) : A ≼ B := ⟨A.id, into_of_into_ran_sub h id_into, id_oto⟩

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

lemma exists_equin_subset_of_dominated {A B : Set} (h : A ≼ B) : ∃ K : Set, K ⊆ B ∧ K ≈ A :=
begin
  rcases h with ⟨f, finto, foto⟩,
  exact ⟨f.ran, finto.right.right, equin_symm ⟨f, ⟨finto.left, finto.right.left, rfl⟩, foto⟩⟩,
end

lemma finite_of_dominated_by_finite {B : Set} (hB : B.is_finite) {A : Set} (hAB : A ≼ B) : A.is_finite :=
begin
  obtain ⟨K, hKB, hKA⟩ := exists_equin_subset_of_dominated hAB,
  exact finite_of_equin_finite (subset_finite_of_finite hB hKB) hKA,
end

lemma infinite_of_dominates_infinite {A : Set} (hA : ¬ A.is_finite) {B : Set} (hAB : A ≼ B) : ¬ B.is_finite :=
begin
  intro hfin, apply hA, exact finite_of_dominated_by_finite hfin hAB,
end

local attribute [instance] classical.prop_decidable

lemma zero_card_le {κ : Set} (hκ : κ.is_cardinal) : card_le ∅ κ :=
begin
  rcases hκ with ⟨K, hK⟩, rw [←hK, ←card_nat zero_nat], apply card_le_of_subset,
  intros z hz, exfalso, exact mem_empty _ hz,
end

lemma finite_card_lt_aleph_null {n : Set} (hn : n.finite_cardinal) : n.card_lt ℵ₀ :=
begin
  rw finite_cardinal_iff_nat at hn, rw [←card_nat hn, card_lt], split,
    apply card_le_of_subset, exact subset_nat_of_mem_nat hn,
  intro h, apply nat_infinite, rw card_equiv at h, exact ⟨_, hn, equin_symm h⟩,
end

lemma finite_card_lt_aleph_null' {X : Set} (Xfin : X.is_finite) : X.card.card_lt ℵ₀ :=
finite_card_lt_aleph_null ⟨_, Xfin, rfl⟩

lemma finite_card_le_iff_le {m : Set} (hm : m.finite_cardinal) {n : Set} (hn : n.finite_cardinal) : m.card_le n ↔ m ≤ n :=
begin
  split,
  { intro h,
    rw finite_cardinal_iff_nat at hn hm,
    rw [←card_nat hm, ←card_nat hn, card_le_iff_equin'] at h,
    apply le_of_not_lt hn hm, intro hnm, rw ←nat_ssub_iff_mem hn hm at hnm,
    rcases h with ⟨f, finto, foto⟩,
    exact pigeonhole'' (ssub_of_sub_of_ssub finto.right.right hnm) ⟨f, onto_ran_of_into finto, foto⟩ (nat_finite hm), },
  { intro h,
    rw finite_cardinal_iff_nat at hn hm,
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

lemma card_lt_trans {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) (hκμ : κ.card_lt μ) {ν : Set} (hμν : μ.card_lt ν) : κ.card_lt ν :=
begin
  rcases hκμ with ⟨κlμ, κeμ⟩, rcases hμν with ⟨μlν, μeν⟩,
  refine ⟨card_le_trans hμ κlμ μlν, λ κeν, _⟩,
  subst κeν, apply κeμ, exact card_eq_of_le_of_le hκ hμ κlμ μlν,
end

lemma card_lt_of_le_of_lt {κ : Set} (κcard : κ.is_cardinal) {μ : Set} (μcard : μ.is_cardinal) (κμ : κ.card_le μ) {ν : Set} (μν : μ.card_lt ν) : κ.card_lt ν :=
begin
  rw card_le_iff at κμ, cases κμ,
    exact card_lt_trans κcard μcard κμ μν,
  subst κμ, exact μν,
end

-- Too lazy to do all of theorem 6L

-- Theorem 6L part a
theorem card_add_le_of_le_left {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) (hκμ : κ.card_le μ)
{ν : Set} (hν : ν.is_cardinal) : (κ.card_add ν).card_le (μ.card_add ν) :=
begin
  rcases hκ with ⟨K, hK⟩,
  rcases hμ with ⟨M, hM⟩,
  rcases hν with ⟨N, hN⟩,
  let M' := M.prod {∅},
  let N' := N.prod {one},
  have hM' : M'.card = μ, rw ←hM, exact same_card,
  have hN' : N'.card = ν, rw ←hN, exact same_card,
  have hdisj : M' ∩ N' = ∅ := disj zero_ne_one,
  rw [←hK, ←hM', card_le_iff_equin', dominated_iff] at hκμ,
  rcases hκμ with ⟨K', hKM', hK'⟩,
  have hdisj' : K' ∩ N' = ∅, rw eq_empty, intros x hx, rw mem_inter at hx,
    apply mem_empty x, rw ←hdisj, rw mem_inter, exact ⟨hKM' hx.left, hx.right⟩,
  rw [←card_equiv, hK] at hK',
  rw [←card_add_spec hK'.symm hN' hdisj', ←card_add_spec hM' hN' hdisj],
  apply card_le_of_subset, apply union_subset_of_subset_of_subset,
    exact subset_trans hKM' subset_union_left,
  exact subset_union_right,
end

theorem card_add_le_of_le_right {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) (hκμ : κ.card_le μ)
{ν : Set} (hν : ν.is_cardinal) : (ν.card_add κ).card_le (ν.card_add μ) :=
begin
  rw [card_add_comm hν hκ, card_add_comm hν hμ], exact card_add_le_of_le_left hκ hμ hκμ hν,
end

-- Theorem 6L part b
theorem card_mul_le_of_le {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) (hκμ : κ.card_le μ)
{ν : Set} (hν : ν.is_cardinal) : (κ.card_mul ν).card_le (μ.card_mul ν) :=
begin
  obtain ⟨K, M, hKM, hK, hM⟩ := exists_sets_of_card_le hκ hμ hκμ,
  rcases hν with ⟨N, hN⟩,
  rw [←card_mul_spec hK hN, ←card_mul_spec hM hN],
  exact card_le_of_subset (prod_subset_of_subset_of_subset hKM subset_self),
end

-- Theorem 6L part c
theorem card_exp_le_of_le {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) (hκμ : κ.card_le μ)
{ν : Set} (hν : ν.is_cardinal) : (κ.card_exp ν).card_le (μ.card_exp ν) :=
begin
  obtain ⟨K, M, hKM, hK, hM⟩ := exists_sets_of_card_le hκ hμ hκμ,
  rcases hν with ⟨N, hN⟩,
  rw [←card_exp_spec hK hN, ←card_exp_spec hM hN],
  apply card_le_of_subset, intros f hf, rw mem_into_funs at *,
  exact ⟨hf.left, hf.right.left, subset_trans hf.right.right hKM⟩,
end

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

lemma Union_chain_is_function {𝓑 : Set} (hch : 𝓑.is_chain) (hf : ∀ {f : Set}, f ∈ 𝓑 → f.is_function) : 𝓑.Union.is_function :=
begin
  rw is_function_iff, split,
    intros b hb, rw mem_Union at hb, rcases hb with ⟨B, hB𝓑, hbB⟩, specialize hf hB𝓑,
    replace hf := hf.left, exact hf _ hbB,
  intros x y y' hxy hxy', simp only [mem_Union, exists_prop] at hxy hxy',
  rcases hxy with ⟨Z, hZ𝓑, hxyZ⟩, rcases hxy' with ⟨Z', hZ𝓑', hxyZ'⟩,
  specialize hch hZ𝓑 hZ𝓑', cases hch,
    specialize hf hZ𝓑', rw is_function_iff at hf, exact hf.right _ _ _ (hch hxyZ) hxyZ',
  specialize hf hZ𝓑, rw is_function_iff at hf, exact hf.right _ _ _ hxyZ (hch hxyZ'),
end

lemma Union_chain_oto {𝓑 : Set} (hch : 𝓑.is_chain) (hf : ∀ {f : Set}, f ∈ 𝓑 → f.one_to_one) : 𝓑.Union.one_to_one :=
begin
  rw one_to_one_iff, intros y x x' hxy hxy', rw mem_Union at hxy hxy',
  rcases hxy with ⟨B, hB𝓑, hxyB⟩, rcases hxy' with ⟨B', hB𝓑', hxyB'⟩,
  specialize hch hB𝓑 hB𝓑', cases hch,
    replace hB𝓑' := hf hB𝓑', rw one_to_one_iff at hB𝓑',
    exact hB𝓑' (hch hxyB) hxyB',
  replace hB𝓑 := hf hB𝓑, rw one_to_one_iff at hB𝓑,
  exact hB𝓑 hxyB (hch hxyB'),
end

theorem choice_equiv_6_1 : Axiom_of_choice_VI.{u} → Axiom_of_choice_I.{u} :=
begin
  dsimp [Axiom_of_choice_VI, Axiom_of_choice_I], intros ax6 R hR,
  let 𝓐 : Set := {f ∈ R.powerset | f.is_function},
  have huncl : ∀ 𝓑 : Set, 𝓑.is_chain → 𝓑 ⊆ 𝓐 → 𝓑.Union ∈ 𝓐,
    intros 𝓑 hch h𝓑𝓐, simp only [mem_sep, mem_powerset], split,
      apply Union_subset_of_subset_powerset, intros B hB,
      have h : B ∈ 𝓐 := h𝓑𝓐 hB,
      rw Set.mem_sep at h, exact h.left,
    apply Union_chain_is_function hch, intros f hf, specialize h𝓑𝓐 hf, rw mem_sep at h𝓑𝓐, exact h𝓑𝓐.right,
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

theorem choice_equiv_6_5 : Axiom_of_choice_VI.{u} → Axiom_of_choice_V.{u} :=
begin
  dsimp [Axiom_of_choice_VI, Axiom_of_choice_V], intros ax6 C D,
  let 𝓐 : Set := {f ∈ (C.prod D).powerset | f.is_function ∧ f.one_to_one},
  have h𝓐 : ∀ {f}, f ∈ 𝓐 ↔ f ⊆ C.prod D ∧ f.is_function ∧ f.one_to_one,
    simp only [mem_sep, mem_powerset, iff_self, implies_true_iff],
  have h𝓐' : ∀ {f : Set}, f ∈ 𝓐 → f.dom ⊆ C ∧ f.ran ⊆ D, intros f hf, rw h𝓐 at hf, split,
      intros x hx, rw mem_dom at hx, rcases hx with ⟨y, hxy⟩,
      have hxy' : x.pair y ∈ C.prod D := hf.left hxy,
      rw pair_mem_prod at hxy', exact hxy'.left,
    intros y hy, rw mem_ran at hy, rcases hy with ⟨x, hxy⟩,
    have hxy' : x.pair y ∈ C.prod D := hf.left hxy,
    rw pair_mem_prod at hxy', exact hxy'.right,
  have huncl : ∀ 𝓑 : Set, 𝓑.is_chain → 𝓑 ⊆ 𝓐 → 𝓑.Union ∈ 𝓐,
    intros 𝓑 hch 𝓑𝓐, rw h𝓐, split,
      intros z hz, rw mem_Union at hz, rcases hz with ⟨B, hB𝓑, hzB⟩, specialize 𝓑𝓐 hB𝓑, rw h𝓐 at 𝓑𝓐,
      exact 𝓑𝓐.left hzB,
    split,
      apply Union_chain_is_function hch, intros f hf, specialize 𝓑𝓐 hf, rw h𝓐 at 𝓑𝓐, exact 𝓑𝓐.right.left,
    apply Union_chain_oto hch, intros f hf, specialize 𝓑𝓐 hf, rw h𝓐 at 𝓑𝓐, exact 𝓑𝓐.right.right,
  specialize ax6 _ huncl, rcases ax6 with ⟨F, hF𝓐, hmax⟩,
  specialize h𝓐' hF𝓐, rw h𝓐 at hF𝓐,
  suffices h : C ⊆ F.dom ∨ D ⊆ F.ran, cases h,
      left, refine ⟨_, ⟨hF𝓐.right.left, _, h𝓐'.right⟩, hF𝓐.right.right⟩,
      rw eq_iff_subset_and_subset, exact ⟨h𝓐'.left, h⟩,
    right, refine ⟨F.inv, ⟨_, _, _⟩, _⟩,
          rw T3F_a, exact hF𝓐.right.right,
        rw [T3E_a, eq_iff_subset_and_subset], exact ⟨h𝓐'.right, h⟩,
      rw T3E_b, exact h𝓐'.left,
    rw ←(T3F_b hF𝓐.right.left.left), exact hF𝓐.right.left,
  apply classical.by_contradiction, intro hns,
  simp only [not_or_distrib, subset_def, not_forall] at hns,
  rcases hns with ⟨⟨c, hcC, hnc⟩, d, hdD, hnd⟩,
  let F' : Set := F ∪ {c.pair d},
  apply hmax F',
      rw h𝓐, split,
        apply union_subset_of_subset_of_subset hF𝓐.left, simp only [subset_def, mem_singleton],
        intros z hz, subst hz, rw pair_mem_prod, exact ⟨hcC, hdD⟩,
      split,
        exact union_singleton_is_fun hF𝓐.right.left hnc,
      exact union_singleton_one_to_one hF𝓐.right.right hnd,
    intros he,
    have hcdF' : c.pair d ∈ F', rw [mem_union, mem_singleton], right, refl,
    rw he at hcdF', apply hnc, rw mem_dom, exact ⟨_, hcdF'⟩,
  exact subset_union_left,
end

-- Theorem 6M completed
theorem choice_equiv_all : list.tfae [
  Axiom_of_choice_I.{u},
  Axiom_of_choice_II.{u},
  Axiom_of_choice_III.{u},
  Axiom_of_choice_IV.{u},
  Axiom_of_choice_V.{u},
  Axiom_of_choice_VI.{u},
  WO.{u}] :=
begin
  tfae_have : 1 → 2, refine list.tfae_prf choice_equiv _ _, finish, finish,
  tfae_have : 2 → 4, refine list.tfae_prf choice_equiv _ _, finish, finish,
  tfae_have : 4 → 3, refine list.tfae_prf choice_equiv _ _, finish, finish,
  tfae_have : 3 → 1, refine list.tfae_prf choice_equiv _ _, finish, finish,
  tfae_have : 6 → 1, exact choice_equiv_6_1,
  tfae_have : 6 → 5, exact choice_equiv_6_5,
  tfae_have : 3 → 7, exact choice_equiv_3_WO,
  tfae_have : 5 → 7, exact choice_equiv_5_WO,
  tfae_have : 7 → 6, exact choice_equiv_WO_6,
  tfae_finish,
end

lemma ax_ch_6 : Axiom_of_choice_VI :=
begin
  refine list.tfae_prf choice_equiv_all _ _ @ax_ch_3, finish, finish,
end
lemma ax_ch_5 : Axiom_of_choice_V :=
begin
  refine list.tfae_prf choice_equiv_all _ _ @ax_ch_3, finish, finish,
end

lemma dominates_of_onto_fun {A B : Set} (he : ∃ f : Set, f.onto_fun A B) : B.dominated A :=
begin
  rcases he with ⟨f, fonto⟩,
  obtain ⟨g, ginto, hc⟩ := (T3J_b (into_of_onto fonto)).mpr fonto,
  exact ⟨g, ginto, one_to_one_of_has_left_inv ginto ⟨_, into_of_onto fonto, hc⟩⟩,
end

lemma exists_onto_of_dominated {A B : Set} (hbne : B.inhab) (hd : B ≼ A) : ∃ g : Set, g.onto_fun A B :=
begin
  rcases hd with ⟨f, finto, foto⟩, rw ←T3J_a finto hbne at foto,
  rcases foto with ⟨g, ginto, gc⟩, use g, rw ←T3J_b ginto, exact ⟨_, finto, gc⟩,
end

lemma dominated_iff_exists_onto_fun {A B : Set} (hbne : B.inhab) : B ≼ A ↔ ∃ f : Set, f.onto_fun A B :=
⟨λ h, exists_onto_of_dominated hbne h, λ h, dominates_of_onto_fun h⟩

lemma nonempty_diff_of_finite_subset_of_inf {A : Set} (hA : ¬ A.is_finite) {B : Set} (hB : B.is_finite) (hBA : B ⊆ A) : A \ B ≠ ∅ :=
begin
  intro he, simp only [eq_empty, mem_diff, not_and_distrib, ←imp_iff_not_or, not_not, ←subset_def] at he,
  have he' : A = B, rw eq_iff_subset_and_subset, exact ⟨he, hBA⟩,
  subst he', exact hA hB,
end

lemma singleton_finite {x : Set} : is_finite {x} :=
begin
  refine ⟨one, one_nat, _⟩,
  dsimp [one, succ], rw [union_empty],
  exact singleton_equin,
end

-- Theorem 6N part a
theorem omega_least_infinite_set {A : Set.{u}} (hA : ¬ A.is_finite) : ω ≼ A :=
begin
  let P : Set := {x ∈ A.powerset | x.is_finite},
  have hP : P ⊆ A.powerset, intros x hx, rw [mem_sep] at hx, exact hx.left,
  obtain ⟨F, Ffun, Fdom, hF⟩ := @ax_ch_3 A,
  have Fran : F.ran ⊆ A, intros y hy, rw mem_ran at hy, rcases hy with ⟨x, hxy⟩,
    have hd : x ∈ F.dom, rw mem_dom, exact ⟨_, hxy⟩,
    specialize hF _ hd, rw [Fdom, mem_sep, mem_powerset] at hd, apply hd.left,
    rw fun_value_def Ffun hxy, exact hF,
  let hrec : Set := pair_sep_eq P P (λ a, a ∪ {F.fun_value (A \ a)}),
  let h : Set := P.rec_fun ∅ hrec,
  have hesA : ∅ ∈ P, rw [mem_sep, mem_powerset], refine ⟨_, _, zero_nat, equin_refl⟩, intros x hx, exfalso, exact mem_empty _ hx,
  have hrecinto : hrec.into_fun P P, apply pair_sep_eq_into,
    intros a ha, rw [mem_sep, mem_powerset] at *, refine ⟨union_subset_of_subset_of_subset ha.left _, _⟩,
      intros x hx, rw mem_singleton at hx, subst hx,
      have hd : A \ a ∈ F.dom, rw [Fdom, mem_sep, mem_powerset], refine ⟨subset_diff, _⟩,
        apply nonempty_diff_of_finite_subset_of_inf hA ha.right ha.left,
      specialize hF _ hd, rw mem_diff at hF, exact hF.left,
    apply union_finite_of_finite ha.right singleton_finite,
  have hh : ∀ {n : Set.{u}}, n ∈ (ω : Set.{u}) → (h.fun_value n) ⊆ A ∧ (h.fun_value n).is_finite, refine @induction _ _ _,
      rw (recursion_thm hesA hrecinto).left, rw [mem_sep, mem_powerset] at hesA, exact hesA,
    intros n hn hi, rw (recursion_thm hesA hrecinto).right _ hn,
    have hd : h.fun_value n ∈ hrec.dom, rw [hrecinto.right.left, mem_sep, mem_powerset], exact hi,
    rw pair_sep_eq_fun_value hd, refine ⟨union_subset_of_subset_of_subset hi.left _, union_finite_of_finite hi.right singleton_finite⟩,
      intros x hx, rw mem_singleton at hx, subst hx, apply Fran, apply fun_value_def'' Ffun,
      rw [Fdom, mem_sep, mem_powerset], refine ⟨subset_diff, nonempty_diff_of_finite_subset_of_inf hA hi.right hi.left⟩,
  let g : Set := pair_sep_eq ω A (λ n, F.fun_value (A \ h.fun_value n)),
  refine ⟨g, pair_sep_eq_into _, pair_sep_eq_oto _⟩,
    intros n hn, apply Fran, apply fun_value_def'' Ffun, rw [Fdom, mem_sep, mem_powerset],
    refine ⟨subset_diff, nonempty_diff_of_finite_subset_of_inf hA (hh hn).right (hh hn).left⟩,
  have hs : ∀ {n : Set.{u}}, n ∈ (ω : Set.{u}) → ∀ {k : Set.{u}}, k ∈ (ω : Set.{u}) → h.fun_value n ⊆ h.fun_value (n + k),
    intros n hn, apply @induction (λ k, h.fun_value n ⊆ h.fun_value (n + k)),
      rw [add_base hn], exact subset_self,
    intros k hk ih,
    have hnknat : (n + k) ∈ (ω : Set.{u}) := add_into_nat hn hk,
    rw [add_ind hn hk, (recursion_thm hesA hrecinto).right _ hnknat],
    have hd : h.fun_value (n + k) ∈ hrec.dom, rw [hrecinto.right.left, mem_sep, mem_powerset], exact hh hnknat,
    rw pair_sep_eq_fun_value hd, exact subset_union_of_subset ih,
  have hlt : ∀ {n : Set.{u}}, n ∈ (ω : Set.{u}) → ∀ {m : Set.{u}}, m ∈ (ω : Set.{u}) → n ∈ m → F.fun_value (A \ h.fun_value n) ≠ F.fun_value (A \ h.fun_value m),
    intros n hn m hm hnm he,
    rw [mem_iff_succ_le hn hm, le_iff_exists (nat_induct.succ_closed hn) hm] at hnm,
    rcases hnm with ⟨p, hp, hnpm⟩,
    specialize hs (nat_induct.succ_closed hn) hp, rw hnpm at hs,
    have hf : F.fun_value (A \ h.fun_value n) ∈ h.fun_value m, apply hs,
      rw (recursion_thm hesA hrecinto).right _ hn,
      have hd : h.fun_value n ∈ hrec.dom, rw [hrecinto.right.left, mem_sep, mem_powerset], exact hh hn,
      rw [pair_sep_eq_fun_value hd, mem_union, mem_singleton], right, refl,
    have hf' : F.fun_value (A \ h.fun_value m) ∉ h.fun_value m,
      have hd : A \ h.fun_value m ∈ F.dom, rw [Fdom, mem_sep, mem_powerset],
        refine ⟨subset_diff, nonempty_diff_of_finite_subset_of_inf hA (hh hm).right (hh hm).left⟩,
      specialize hF _ hd, rw [mem_diff] at hF, exact hF.right,
    change F.fun_value (A \ h.fun_value n) = F.fun_value (A \ h.fun_value m) at he,
    rw he at hf, exact hf' hf,
  intros n hn m hm he, apply classical.by_contradiction, intro hne,
  cases nat_order_conn hn hm hne with hnm hmn,
    exact hlt hn hm hnm he,
  exact hlt hm hn hmn he.symm,
end

-- Theorem 6N part b
theorem aleph_null_least_infinite_cardinal {κ : Set} (hκ : κ.is_cardinal) (hinf : ¬ κ.finite_cardinal) : card_le ℵ₀ κ :=
begin
  rcases hκ with ⟨K, hK⟩, rw ←hK, rw card_le_iff_equin',
  apply omega_least_infinite_set, intro hf, exact hinf ⟨_, hf, hK⟩,
end

lemma equin_omega_of_inf_subset {A : Set} (hA : ¬ A.is_finite) (hA' : A ⊆ ω) : A ≈ ω :=
equin_of_dom_of_dom (dominated_sub hA') (omega_least_infinite_set hA)

lemma exists_sub_card_alpeh_null_of_inf {κ : Set} (hκ : ¬ κ.finite_cardinal) {B : Set} (hB : B.card = κ) : ∃ A : Set, A ⊆ B ∧ A.card = ℵ₀ :=
begin
  have Binf : ¬ B.is_finite, intro fin, apply hκ, exact ⟨_, fin, hB⟩,
  have h := omega_least_infinite_set Binf,
  obtain ⟨A, hAB, hA⟩ := exists_equin_subset_of_dominated h,
  rw ←card_equiv at hA,
  exact ⟨_, hAB, hA⟩,
end

lemma card_lt_aleph_null_iff_finite {κ : Set} (hκ : κ.is_cardinal) : κ.card_lt ℵ₀ ↔ κ.finite_cardinal :=
begin
  split,
    intros hlt, apply classical.by_contradiction, intro hnf, apply hlt.right,
    apply card_eq_of_le_of_le hκ ⟨_, rfl⟩,
      exact hlt.left,
    exact aleph_null_least_infinite_cardinal hκ hnf,
  intro hf, exact finite_card_lt_aleph_null hf,
end

lemma card_inf_of_ge_inf {κ : Set} (κcard : κ.is_cardinal) (κfin : ¬ κ.finite_cardinal)
  {μ : Set} (μcard : μ.is_cardinal) (κμ : κ.card_le μ) : ¬ μ.finite_cardinal :=
begin
  intro μfin, apply κfin,
  rw ←card_lt_aleph_null_iff_finite κcard,
  rw ←card_lt_aleph_null_iff_finite μcard at μfin,
  exact card_lt_of_le_of_lt κcard μcard κμ μfin,
end

-- Corollary 6G, different proof
theorem subset_finite_of_finite' {A : Set.{u}} (hA : A.is_finite) {B : Set} (hBA : B ⊆ A) : B.is_finite :=
begin
  rcases hA with ⟨n, hn, hAn⟩,
  have hBn : B.card.card_le n.card, rw ←card_equiv at hAn, rw ←hAn, rw card_le_iff_equin', exact dominated_sub hBA,
  have hnal : n.card.card_lt ℵ₀, apply finite_card_lt_aleph_null, exact ⟨_, nat_finite hn, rfl⟩,
  refine one_finite_all_finite _ rfl, rw ←card_lt_aleph_null_iff_finite ⟨_, rfl⟩, split,
    exact card_le_trans ⟨n, rfl⟩ hBn hnal.left,
  intro he, apply hnal.right, apply card_eq_of_le_of_le ⟨_, rfl⟩ ⟨_, rfl⟩ hnal.left,
  rw ←he, exact hBn,
end

-- Corollary 6P
theorem infinite_iff_equin_proper_subset_self {A : Set} : ¬ A.is_finite ↔ ∃ B : Set, B ⊂ A ∧ A ≈ B :=
begin
  split,
    intro hinf,
    obtain ⟨f, finto, foto⟩ := omega_least_infinite_set hinf,
    let L := (f.comp succ_fun).comp f.inv,
    let R := (A \ f.ran).id,
    let g := L ∪ R,
    let B : Set := A \ {f.fun_value ∅},
    refine ⟨B, _, _⟩,
      rw ssubset_iff, refine ⟨subset_diff, _⟩,
      intro he, rw ←ext_iff at he, simp only [and_iff_left_iff_imp, mem_diff, not_forall, mem_singleton] at he,
      refine he (f.fun_value ∅) _ rfl,
      apply finto.right.right, apply fun_value_def'' finto.left, rw finto.right.left, exact zero_nat,
    have ranL : L.ran = f.ran \ {f.fun_value ∅},
      have h : (f.comp succ_fun).dom ⊆ f.inv.ran,
        have h' : succ_fun.ran ⊆ f.dom, rw [succ_fun_ran, finto.right.left], exact subset_diff,
        rw [dom_comp h', T3E_b, finto.right.left, succ_fun_into_fun.right.left], exact subset_self,
      rw [ran_comp h, ran_comp_complex foto, finto.right.left, succ_fun_ran],
      have h' : {∅} ⊆ ω, intros x hx, rw [mem_singleton] at hx, subst hx, exact zero_nat,
      rw [diff_diff_eq_self_of_subset h'],
      have h'' : ∅ ∈ f.dom, rw finto.right.left, exact zero_nat,
      rw img_singleton_eq finto.left h'',
    refine ⟨g, _, _⟩,
      have compfun : (f.comp succ_fun).is_function := T3H_a finto.left succ_fun_into_fun.left,
      have finvfun : f.inv.is_function := T3F_a.mpr foto,
      have domL : L.dom = f.ran,
        have h : f.inv.ran ⊆ (f.comp succ_fun).dom,
          have h' : succ_fun.ran ⊆ f.dom, rw [succ_fun_ran, finto.right.left], exact subset_diff,
          rw [dom_comp h', T3E_b, finto.right.left, succ_fun_into_fun.right.left], exact subset_self,
        rw [dom_comp h, T3E_a],
      have gonto : g.onto_fun (L.dom ∪ R.dom) (L.ran ∪ R.ran),
        apply union_fun (T3H_a compfun finvfun) id_is_function,
        rw [eq_empty, domL, id_into.right.left], intros y hy, rw [mem_inter, mem_diff] at hy,
        exact hy.right.right hy.left,
      rw [domL, id_into.right.left] at gonto,
      have h : f.ran ∪ A \ f.ran = A, rw eq_iff_subset_and_subset,
        refine ⟨union_subset_of_subset_of_subset finto.right.right subset_diff, _⟩,
        intros x hx, rw [mem_union, mem_diff],
        by_cases hc : x ∈ f.ran,
          left, exact hc,
        right, exact ⟨hx, hc⟩,
      rw h at gonto,
      have ranL : L.ran = f.ran \ {f.fun_value ∅},
        have h : (f.comp succ_fun).dom ⊆ f.inv.ran,
          have h' : succ_fun.ran ⊆ f.dom, rw [succ_fun_ran, finto.right.left], exact subset_diff,
          rw [dom_comp h', T3E_b, finto.right.left, succ_fun_into_fun.right.left], exact subset_self,
        rw [ran_comp h, ran_comp_complex foto, finto.right.left, succ_fun_ran],
        have h' : {∅} ⊆ ω, intros x hx, rw [mem_singleton] at hx, subst hx, exact zero_nat,
        rw [diff_diff_eq_self_of_subset h'],
        have h'' : ∅ ∈ f.dom, rw finto.right.left, exact zero_nat,
        rw img_singleton_eq finto.left h'',
      rw [ranL, id_onto.right.right] at gonto,
      have h' : f.ran \ {f.fun_value ∅} ∪ A \ f.ran = B, apply ext,
        simp only [mem_diff, mem_singleton, mem_union], intro y, split,
          rintro (⟨hy, hny⟩|⟨hy, hny⟩),
            exact ⟨finto.right.right hy, hny⟩,
          refine ⟨hy, _⟩, intro hy', apply hny, subst hy', apply fun_value_def'' finto.left, rw finto.right.left, exact zero_nat,
        rintro ⟨hy, hny⟩, by_cases hc : y ∈ f.ran,
          left, exact ⟨hc, hny⟩,
        right, exact ⟨hy, hc⟩,
      rw h' at gonto, exact gonto,
    refine union_one_to_one _ id_oto _,
      rw [←T3F_a, T3I, T3E_c finto.left.left, T3I], apply T3H_a finto.left, apply T3H_a,
        rw T3F_a, exact succ_one_to_one,
      rw T3F_a, exact foto,
    rw [ranL, id_onto.right.right, eq_empty], simp only [mem_inter, mem_diff, mem_singleton],
    rintros y ⟨⟨hy, hny⟩, hA, hnf⟩, exact hnf hy,
  rintro ⟨B, hBA, heq⟩, exact pigeonhole'' hBA heq,
end

-- I skipped some of the section on countable sets

def countable (A : Set) : Prop := A ≼ ω

lemma countable_card {A : Set} : A.card.card_le ℵ₀ ↔ A.countable :=
begin
  rw [card_le_iff_equin', countable],
end

lemma countable_iff {A : Set} : A.countable ↔ A.is_finite ∨ A.card = ℵ₀  :=
by rw [←countable_card, card_le_iff, card_lt_aleph_null_iff_finite ⟨_, rfl⟩, card_finite_iff_finite]

lemma card_lt_of_not_le {K M : Set} (h : ¬ K.card.card_le M.card) : M.card.card_lt K.card :=
begin
  rw card_lt_iff, split,
    cases ax_ch_5 K M with hKM hMK,
      exfalso, apply h, rw card_le_iff_equin', exact hKM,
    exact hMK,
  intro he, apply h, rw ←card_equiv at he, rw card_le_iff, right, exact he.symm,
    
end

lemma nat_le_inf {n : Set} (hn : n ∈ ω) {K : Set} (hK : ¬ K.is_finite) : n.card_le K.card :=
begin
  apply card_le_trans ⟨ω, rfl⟩,
    have h : n.card_lt ℵ₀, rw card_lt_aleph_null_iff_finite ⟨_, card_nat hn⟩,
      rw finite_cardinal_iff_nat, exact hn,
    exact h.left,
  apply aleph_null_least_infinite_cardinal ⟨_, rfl⟩, rw card_finite_iff_finite, exact hK,
end

lemma nat_le_inf' {n : Set} (hn : n ∈ ω) {κ : Set} (hκ : κ.is_cardinal) (hinf : ¬ κ.finite_cardinal) : n.card_le κ :=
begin
  rcases hκ with ⟨K, hK⟩, rw ←hK, apply nat_le_inf hn, rw ←card_finite_iff_finite, rw hK, exact hinf,
end

lemma finite_le_infinite {K : Set} (hK : K.is_finite) {M : Set} (hM : ¬ M.is_finite) : K.card.card_le M.card :=
begin
  rw finite_iff at hK, rcases hK with ⟨n, hn, he⟩, rw he, exact nat_le_inf hn hM,
end

lemma finite_le_infinite' {κ : Set} (hκ : κ.is_cardinal) (hfin : κ.finite_cardinal) {μ : Set} (hμ : μ.is_cardinal) (hinf : ¬ μ.finite_cardinal) : κ.card_le μ :=
begin
  rcases hκ with ⟨K, hK⟩, rcases hμ with ⟨M, hM⟩, rw [←hK] at *,
  rw ←hM at hinf, rw ←hM, rw card_finite_iff_finite at *, exact finite_le_infinite hfin hinf,
end

lemma mul_infinite_card_eq_self {κ : Set.{u}} (hκ : κ.is_cardinal) (hinf : ¬ κ.finite_cardinal) : κ.card_mul κ = κ :=
begin
  rcases hκ with ⟨B, hB⟩,
  let H : Set := {f ∈ ((B.prod B).prod B).powerset | f = ∅ ∨ ∃ A : Set, ¬ A.is_finite ∧ A ⊆ B ∧ (A.prod A).correspondence A f},
  have hH : ∀ {f : Set}, f ∈ H ↔ f = ∅ ∨ ∃ A : Set, ¬ A.is_finite ∧ A ⊆ B ∧ (A.prod A).correspondence A f,
    simp only [mem_powerset, and_imp, forall_eq_or_imp, mem_sep, and_iff_right_iff_imp, exists_imp_distrib],
    refine ⟨empty_subset, _⟩, rintros f A hAinf hAB ⟨fonto, foto⟩, refine subset_trans _ (prod_subset_of_subset_of_subset (prod_subset_of_subset_of_subset hAB hAB) hAB),
    rw [←fonto.right.left, ←fonto.right.right, ←rel_sub_dom_ran], exact fonto.left.left,
  have hch : ∀ C : Set, C.is_chain → C ⊆ H → C.Union ∈ H, intros C hch hCH,
    by_cases case : ∃ h, h ∈ C ∧ h ≠ ∅,
      rcases case with ⟨h, hh, hhne⟩, rw hH, right,
      let A := {R ∈ B.powerset | ∃ f : Set, f ∈ C ∧ R = f.ran}.Union,
      have hA : ∀ ⦃y⦄, y ∈ A ↔ ∃ f : Set, y ∈ f.ran ∧ f ∈ C,
        simp only [mem_powerset, exists_prop, mem_Union, mem_sep, mem_ran], intro y, split,
          rintro ⟨A, ⟨hA, f, hf, he⟩, hy⟩, subst he, rw mem_ran at hy, exact ⟨_, hy, hf⟩,
        rintro ⟨f, hy, hf⟩, rw ←mem_ran at hy,
        have h : f ∈ H := hCH hf,
        rw hH at h, rcases h with (hf|⟨A, -, hAB, fonto, -⟩),
          subst hf, rw [ran_empty_eq_empty] at hy, exfalso, exact mem_empty _ hy,
        refine ⟨_, ⟨_, _, hf, rfl⟩, hy⟩, rw fonto.right.right, exact hAB,
      have hAeq : A = C.Union.ran := ran_Union_eq_Union_ran hA,
      let D := {D ∈ (B.prod B).powerset | ∃ f : Set, f ∈ C ∧ D = f.dom}.Union,
      have hD : ∀ ⦃x⦄, x ∈ D ↔ ∃ f : Set, x ∈ f.dom ∧ f ∈ C,
        simp only [mem_Union, mem_sep, mem_powerset, exists_prop, mem_dom], intro x, split,
          rintro ⟨X, ⟨hX, f, hf, he⟩, hx⟩, subst he, rw mem_dom at hx, exact ⟨_, hx, hf⟩,
        rintro ⟨f, hx, hf⟩, rw ←mem_dom at hx,
        have h : f ∈ H := hCH hf,
        rw hH at h, rcases h with (hf|⟨A, -, hAB, fonto, -⟩),
          subst hf, rw [dom_empty_eq_empty] at hx, exfalso, exact mem_empty _ hx,
        refine ⟨_, ⟨_, _, hf, rfl⟩, hx⟩, rw fonto.right.left, exact prod_subset_of_subset_of_subset hAB hAB,
      have hDeq : D = C.Union.dom := dom_Union_eq_Union_dom hD,
      refine ⟨A, _, _, ⟨_, _, hAeq.symm⟩, _⟩,
      { have hhC := hCH hh,
        rw hH at hhC, rcases hhC with (hemp|⟨A', hA'inf, hA'B, honto, hoto⟩),
          exfalso, exact hhne hemp,
        intro hAfin, apply hA'inf,
        have hA'subA : A' ⊆ A, rw ←honto.right.right, intros y hy, rw hA, exact ⟨_, hy, hh⟩,
        exact subset_finite_of_finite hAfin hA'subA, },
      { intros y hy, rw hA at hy, rcases hy with ⟨f, hy, hf⟩,
        replace hf := hCH hf, rw hH at hf, rcases hf with (hf|⟨A, -, hAB, fonto, -⟩),
          subst hf, rw [ran_empty_eq_empty] at hy, exfalso, exact mem_empty _ hy,
        rw fonto.right.right at hy, exact hAB hy, },
      { apply Union_chain_is_function hch, intros f hf,
        replace hf := hCH hf, rw hH at hf, rcases hf with (hf|⟨A, -, -, fonto, -⟩),
          subst hf, exact empty_fun,
        exact fonto.left, },
      { apply ext, intro z, split,
          rw [←hDeq, hD], rintro ⟨f, hz, hf⟩,
          have hf' := hCH hf, rw hH at hf', rcases hf' with (hf'|⟨X, Xinf, hXB, fonto, foto⟩),
            subst hf', rw dom_empty_eq_empty at hz, exfalso, exact mem_empty _ hz,
          simp only [fonto.right.left, mem_prod, exists_prop] at hz, rcases hz with ⟨a₁, ha₁, a₂, ha₂, he⟩, subst he,
          simp only [pair_mem_prod, hA], rw ←fonto.right.right at ha₁ ha₂,
          exact ⟨⟨_, ha₁, hf⟩, _, ha₂, hf⟩,
        simp only [mem_prod, exists_prop, hA],
        have hpart : ∀ {f₁ : Set.{u}}, f₁ ∈ C → ∀ {f₂}, f₂ ∈ C → f₁ ⊆ f₂ → ∀ {a₁ : Set}, a₁ ∈ f₁.ran ∪ f₂.ran → ∀ {a₂}, a₂ ∈ f₁.ran ∪ f₂.ran → a₁.pair a₂ ∈ C.Union.dom,
          intros f₁ hf₁ f₂ hf₂ hf a₁ ha₁ a₂ ha₂,
          have hf₂' := hCH hf₂, rw hH at hf₂', rcases hf₂' with (hf₂'|⟨X, Xinf, hXB, fonto, foto⟩),
            subst hf₂', rw [ran_empty_eq_empty, union_empty, mem_ran] at ha₂, rcases ha₂ with ⟨x, ha₂⟩, exfalso, exact mem_empty _ (hf ha₂),
          rw [←hDeq, hD], refine ⟨f₂, _, hf₂⟩, rw [fonto.right.left, pair_mem_prod],
          replace ha₁ :=  union_subset_of_subset_of_subset (ran_subset_of_subset hf) subset_self ha₁,
          replace ha₂ :=  union_subset_of_subset_of_subset (ran_subset_of_subset hf) subset_self ha₂,
          rw fonto.right.right at ha₁ ha₂, exact ⟨ha₁, ha₂⟩,

        rintro ⟨a₁, ⟨f₁, ha₁, hf₁⟩, a₂, ⟨f₂, ha₂, hf₂⟩, he⟩, subst he,
        replace ha₁ : a₁ ∈ f₁.ran ∪ f₂.ran, rw mem_union, left, exact ha₁,
        replace ha₂ : a₂ ∈ f₁.ran ∪ f₂.ran, rw mem_union, right, exact ha₂,
        cases hch hf₁ hf₂ with hf hf,
          exact hpart hf₁ hf₂ hf ha₁ ha₂,
        rw union_comm at ha₁ ha₂,
        exact hpart hf₂ hf₁ hf ha₁ ha₂, },
      { apply Union_chain_oto hch, intros f hf,
        replace hf := hCH hf, rw hH at hf, rcases hf with (hf|⟨-, -, -, -, foto⟩),
          subst hf, exact empty_oto,
        exact foto, },
    rw hH, left, rw eq_empty, intros z hz, apply case, rw mem_Union at hz,
    rcases hz with ⟨f, hf, hz⟩, refine ⟨_, hf, _⟩, exact ne_empty_of_inhabited _ ⟨_, hz⟩,
  obtain ⟨f₀, hf₀, hmax⟩ := ax_ch_6 _ hch,
  rw hH at hf₀, cases hf₀,
    obtain ⟨A, hAB, hA⟩ := exists_sub_card_alpeh_null_of_inf hinf hB,
    have hAprodA := aleph_mul_aleph_eq_aleph,
    rw [←hA, ←card_mul_spec rfl rfl, card_equiv] at hAprodA, rcases hAprodA with ⟨g, gcorr⟩,
    have gH : g ∈ H, rw hH, right, refine ⟨_, _, hAB, gcorr⟩, rw [←card_finite_iff_finite, hA], exact aleph_null_infinite_cardinal,
    have Ainhab : A.inhab, rw card_equiv at hA, replace hA := equin_symm hA,
      rcases hA with ⟨f, fonto, foto⟩, use f.fun_value ∅, rw ←fonto.right.right,
      apply fun_value_def'' fonto.left, rw fonto.right.left, exact zero_nat,
    rcases Ainhab with ⟨a, ha⟩,
    exfalso, subst hf₀, refine hmax _ gH _ empty_subset,
    apply ne_empty_of_inhabited, use (pair a a).pair (g.fun_value (a.pair a)),
    apply fun_value_def' gcorr.onto.left, rw [gcorr.onto.right.left, pair_mem_prod], exact ⟨ha, ha⟩,
  rcases hf₀ with ⟨A₀, hAinf, hAB, fcorr⟩,
  let μ := A₀.card,
  have μpμ : μ.card_mul μ = μ, rw [←card_mul_spec rfl rfl, card_equiv], exact ⟨_, fcorr⟩,
  have hlt : (B \ A₀).card.card_lt μ, apply card_lt_of_not_le, intro hle,
    rw card_le_iff_equin' at hle,
    obtain ⟨D, hDBA, hDA⟩ := exists_equin_subset_of_dominated hle,
    rw ←card_equiv at hDA,
    have hdisj : A₀ ∩ D = ∅, rw eq_empty, intros x hx, rw mem_inter at hx,
      specialize hDBA hx.right, rw mem_diff at hDBA, exact hDBA.right hx.left,
    have hmpm : μ.card_add μ = μ,
      rw [card_add_self_eq_two_mul_self ⟨_, rfl⟩],
      apply card_eq_of_le_of_le (mul_cardinal (nat_is_cardinal two_nat) ⟨_, rfl⟩) ⟨_, rfl⟩,
        change (two.card_mul μ).card_le μ,
        nth_rewrite 1 ←μpμ, refine card_mul_le_of_le (nat_is_cardinal two_nat) ⟨_, rfl⟩ _ ⟨_, rfl⟩,
        have two_le_a : two.card_le ℵ₀, rw card_le_iff, left, apply finite_card_lt_aleph_null,
          rw finite_cardinal_iff_nat, exact two_nat,
        refine card_le_trans ⟨_, rfl⟩ two_le_a _, apply aleph_null_least_infinite_cardinal ⟨_, rfl⟩,
        rw card_finite_iff_finite, exact hAinf,
      nth_rewrite 0 ←card_mul_one_eq_self ⟨_, rfl⟩,
      rw card_mul_comm ⟨_, rfl⟩ (nat_is_cardinal one_nat),
      refine card_mul_le_of_le (nat_is_cardinal one_nat) (nat_is_cardinal two_nat) _ ⟨_, rfl⟩,
      have one_fin : one.finite_cardinal, rw finite_cardinal_iff_nat, exact one_nat,
      have two_fin : two.finite_cardinal, rw finite_cardinal_iff_nat, exact two_nat,
      rw [finite_card_le_iff_le one_fin two_fin, le_iff, two],
      left, exact self_mem_succ,
    have cardAD : (A₀ ∪ D).card = μ, rw card_add_spec rfl hDA hdisj, exact hmpm,
    have hext : ((D.prod A₀) ∪ ((A₀.prod D) ∪ (D.prod D))).card = D.card,
      have hdisj' : A₀.prod D ∩ D.prod D = ∅, rw rel_eq_empty (inter_rel_is_rel prod_is_rel),
        simp only [eq_empty, mem_inter] at hdisj,
        simp only [pair_mem_prod, mem_inter], rintros x y ⟨⟨hx, hy⟩, hx', hy'⟩, exact hdisj _ ⟨hx, hx'⟩,
      have hdisj'' : D.prod A₀ ∩ (A₀.prod D ∪ D.prod D) = ∅, rw rel_eq_empty (inter_rel_is_rel prod_is_rel),
        simp only [eq_empty, mem_inter] at hdisj,
        simp only [pair_mem_prod, mem_inter, mem_union], rintros x y ⟨⟨hx, hy⟩, (⟨hx', hy'⟩|⟨hx', hy'⟩)⟩,
          exact hdisj _ ⟨hy, hy'⟩,
        exact hdisj _ ⟨hy, hy'⟩,
      rw [card_add_spec rfl rfl hdisj'', card_add_spec rfl rfl hdisj'],
      simp only [card_mul_spec rfl rfl, hDA],
      change (μ.card_mul μ).card_add ((μ.card_mul μ).card_add (μ.card_mul μ)) = μ,
      simp only [μpμ, hmpm],
    rw card_equiv at hext, rcases hext with ⟨g, gcorr⟩,
    have fgonto : (f₀ ∪ g).onto_fun ((A₀ ∪ D).prod (A₀ ∪ D)) (A₀ ∪ D),
      simp only [union_prod, prod_union],
      simp only [←@union_assoc (A₀.prod A₀) (D.prod A₀) ((A₀.prod D) ∪ (D.prod D))],
      rw [←fcorr.onto.right.left, ←gcorr.onto.right.left, ←fcorr.onto.right.right, ←gcorr.onto.right.right],
      apply union_fun fcorr.onto.left gcorr.onto.left,
      rw [fcorr.onto.right.left, gcorr.onto.right.left],
      rw rel_eq_empty (inter_rel_is_rel prod_is_rel),
      intros x y hxy, simp only [mem_inter, mem_union, pair_mem_prod] at hxy,
      rw eq_empty at hdisj, simp only [mem_inter] at hdisj,
      rcases hxy with ⟨⟨hx', hy'⟩,(⟨hx, hy⟩|⟨hx, hy⟩|⟨hx, hy⟩)⟩,
          exact hdisj _ ⟨hx', hx⟩,
        exact hdisj _ ⟨hy', hy⟩,
      exact hdisj _ ⟨hx', hx⟩,
    have fgH : f₀ ∪ g ∈ H, rw hH, right, refine ⟨A₀ ∪ D, _, _, _⟩,
          rw [←card_finite_iff_finite, cardAD, card_finite_iff_finite], exact hAinf,
        apply union_subset_of_subset_of_subset hAB,
        intros x hx, specialize hDBA hx, rw mem_diff at hDBA, exact hDBA.left,
      split,
        exact fgonto,
      apply union_one_to_one fcorr.oto gcorr.oto, rw [fcorr.onto.right.right, gcorr.onto.right.right],
      exact hdisj,
    have Dinhab : D.inhab,
      have a_le_D : card_le ℵ₀ D.card, apply aleph_null_least_infinite_cardinal ⟨_, rfl⟩,
        rw [hDA, card_finite_iff_finite], exact hAinf,
      rw card_le_iff_equin' at a_le_D, rcases a_le_D with ⟨f, finto, foto⟩,
      use f.fun_value ∅, apply finto.right.right, apply fun_value_def'' finto.left,
      rw finto.right.left, exact zero_nat,
    rcases Dinhab with ⟨d, hd⟩,
    have fgnef : f₀ ∪ g ≠ f₀, intro he,
      have hd' : d ∈ (f₀ ∪ g).ran, rw [fgonto.right.right, mem_union], right, exact hd,
      rw [he, fcorr.onto.right.right] at hd', simp only [eq_empty, mem_inter] at hdisj,
      exact hdisj _ ⟨hd', hd⟩,
    exact hmax _ fgH fgnef subset_union_left,
  have kem : κ = μ, symmetry, apply card_eq_of_le_of_le ⟨_, rfl⟩ ⟨_, hB⟩,
      rw ←hB, exact card_le_of_subset hAB,
    rw [←hB, ←union_diff_eq_self_of_subset hAB, card_add_spec rfl rfl self_inter_diff_empty],
    change (A₀.card.card_add (B \ A₀).card).card_le μ, rw ←μpμ, apply card_le_trans (mul_cardinal (nat_is_cardinal two_nat) ⟨A₀, rfl⟩),
      rw ←card_add_self_eq_two_mul_self ⟨_, rfl⟩, exact card_add_le_of_le_right ⟨_, rfl⟩ ⟨_, rfl⟩ hlt.left ⟨_, rfl⟩,
    exact card_mul_le_of_le ⟨_, card_nat two_nat⟩ ⟨_, rfl⟩ (nat_le_inf two_nat hAinf) ⟨_, rfl⟩,
  rw kem, exact μpμ,
end

lemma add_infinite_card_eq_self {κ : Set.{u}} (hκ : κ.is_cardinal) (hinf : ¬ κ.finite_cardinal) : κ.card_add κ = κ :=
begin
  rw [card_add_self_eq_two_mul_self hκ],
  apply card_eq_of_le_of_le (mul_cardinal (nat_is_cardinal two_nat) hκ) hκ,
    nth_rewrite 1 ←mul_infinite_card_eq_self hκ hinf,
    refine card_mul_le_of_le (nat_is_cardinal two_nat) hκ _ hκ,
    have two_le_a : two.card_le ℵ₀, rw card_le_iff, left, apply finite_card_lt_aleph_null,
      rw finite_cardinal_iff_nat, exact two_nat,
    refine card_le_trans ⟨_, rfl⟩ two_le_a (aleph_null_least_infinite_cardinal hκ hinf),
  nth_rewrite 0 ←card_mul_one_eq_self hκ,
  rw card_mul_comm hκ (nat_is_cardinal one_nat),
  refine card_mul_le_of_le (nat_is_cardinal one_nat) (nat_is_cardinal two_nat) _ hκ,
  have one_fin : one.finite_cardinal, rw finite_cardinal_iff_nat, exact one_nat,
  have two_fin : two.finite_cardinal, rw finite_cardinal_iff_nat, exact two_nat,
  rw [finite_card_le_iff_le one_fin two_fin, le_iff, two],
  left, exact self_mem_succ,
end

lemma card_add_eq_right_of_le {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) (hinf : ¬ μ.finite_cardinal) (hκμ : κ.card_le μ) : κ.card_add μ = μ :=
begin
  apply card_eq_of_le_of_le (add_cardinal hκ hμ) hμ,
    nth_rewrite 1 ←add_infinite_card_eq_self hμ hinf,
    exact card_add_le_of_le_left hκ hμ hκμ hμ,
  nth_rewrite 0 ←card_empty_add hμ, refine card_add_le_of_le_left (nat_is_cardinal zero_nat) hκ _ hμ,
  exact zero_card_le hκ,
end

lemma card_add_eq_left_of_le {κ : Set} (hκ : κ.is_cardinal) {μ : Set} (hμ : μ.is_cardinal) (hinf : ¬ μ.finite_cardinal) (hκμ : κ.card_le μ) : μ.card_add κ = μ :=
begin
  rw card_add_comm hμ hκ, exact card_add_eq_right_of_le hκ hμ hinf hκμ,
end

lemma card_diff_from_inf {K : Set} (hinf : ¬ K.is_finite) {M : Set} (hMK : M ⊆ K) (hMK' : M.card.card_lt K.card) : (K \ M).card = K.card :=
begin
  have he : K.card = (M ∪ K \ M).card, rw union_diff_eq_self_of_subset hMK,
  rw card_add_spec rfl rfl self_inter_diff_empty at he,
  by_cases hcase : M.is_finite,
    have hKM : ¬ (K \ M).is_finite, intro hfin, rw finite_iff at *,
      rcases hcase with ⟨n, hn, hM⟩, rcases hfin with ⟨m, hm, hKM⟩, rw [hM, hKM] at he,
      apply hinf, rw he, refine ⟨n + m, add_into_nat hn hm, _⟩,
      apply card_add_eq_ord_add,
        rw finite_cardinal_iff_nat, exact hn,
      rw finite_cardinal_iff_nat, exact hm,
    have hKM' : ¬ (K \ M).card.finite_cardinal, intro hfin, rw card_finite_iff_finite at hfin,
      exact hKM hfin,
    have he' : M.card.card_add (K \ M).card = (K \ M).card,
      apply card_add_eq_right_of_le ⟨_, rfl⟩ ⟨_, rfl⟩ hKM', exact finite_le_infinite hcase hKM,
    rw he' at he, exact he.symm,
  cases ax_ch_5 M (K \ M),
    have hKMfin : ¬ (K \ M).is_finite := infinite_of_dominates_infinite hcase h,
    have he' : M.card.card_add (K \ M).card = (K \ M).card,
      apply card_add_eq_right_of_le ⟨_, rfl⟩ ⟨_, rfl⟩,
        rw card_finite_iff_finite, exact hKMfin,
      rw ←card_le_iff_equin' at h, exact h,
    rw he' at he, exact he.symm,
  have he' : M.card.card_add (K \ M).card = M.card,
    apply card_add_eq_left_of_le ⟨_, rfl⟩ ⟨_, rfl⟩,
      rw card_finite_iff_finite, exact hcase,
    rw ←card_le_iff_equin' at h, exact h,
  rw he' at he, exfalso, exact hMK'.right he.symm,
end

lemma card_exp_self_eq_pow_self {κ : Set} (hκ : κ.is_cardinal) (hinf : ¬ κ.finite_cardinal) : κ.card_exp κ = two.card_exp κ :=
begin
  have two_card : two.is_cardinal := nat_is_cardinal two_nat,
  apply card_eq_of_le_of_le (exp_cardinal hκ hκ) (exp_cardinal two_card hκ),
    nth_rewrite 2 ←mul_infinite_card_eq_self hκ hinf, rw ←card_exp_exp two_card hκ hκ,
    exact card_exp_le_of_le hκ (exp_cardinal two_card hκ) (card_le_iff.mpr (or.inl (card_lt_exp hκ))) hκ,
  refine card_exp_le_of_le two_card hκ (finite_le_infinite' two_card _ hκ hinf) hκ,
  rw finite_cardinal_iff_nat, exact two_nat,
end

end Set
