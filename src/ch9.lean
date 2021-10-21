import ch8
universe u
namespace Set

local attribute [irreducible] mem

-- sections 1 and 2 are mostly skipped

lemma Aleph_le_of_le {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  α.Aleph.card_le β.Aleph ↔ α ≤ β :=
begin
  rw card_le_iff, split,
    rintro (h|h),
      left, exact Aleph_oto' αord βord h,
    right, apply Aleph_oto (succ_ord_of_ord (ord_max_ord αord βord)),
    { rw mem_succ_iff_le, exact ord_max_le_left, },
    { rw mem_succ_iff_le, exact ord_max_le_right αord βord, },
    exact h,
  rintro (h|h),
    left, exact Aleph_lt_of_mem βord h,
  subst h, right, refl,
end

lemma Aleph_oto'' {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) (αβ : α.Aleph = β.Aleph) : α = β :=
begin
  refine Aleph_oto (succ_ord_of_ord (ord_max_ord αord βord)) _ _ αβ; rw mem_succ_iff_le,
    exact ord_max_le_left,
  exact ord_max_le_right αord βord,
end

lemma nat_pos_of_not_empty {n m : Set} (nm : n ∈ m) (mω : m ∈ ω) : ∅ ∈ m :=
begin
  apply classical.by_contradiction, intro h,
  obtain h₂ := le_of_not_lt zero_nat mω h, cases h₂,
    exact mem_empty _ h₂,
  subst h₂, exact mem_empty _ nm,
end

lemma ord_disj {β : Set} (βord : β.is_ordinal) : {β} ∩ β = ∅ :=
begin
  apply classical.by_contradiction, intro h,
  obtain ⟨α, hα⟩ := inhabited_of_ne_empty h, rw [mem_inter, mem_singleton] at hα,
  obtain ⟨αβ, hα⟩ := hα, subst αβ, exact ord_mem_irrefl βord hα,
end

lemma card_empty : card ∅ = ∅ :=
by rw card_nat zero_nat

lemma struct_restrict_eq {α : Set} (αord : α.is_ordinal) {S : Set} (Sα : S ⊆ α) :
  S.eps_order_struct = S.struct_restrict (α.eps_order_struct) :=
begin
  ext; dsimp,
    refl,
  refine rel_ext pair_sep_is_rel (inter_rel_is_rel pair_sep_is_rel) _,
  intros x y, simp only [eps_order, mem_inter, pair_mem_prod, pair_mem_pair_sep], split,
    rintro ⟨xS, yS, xy⟩, exact ⟨⟨Sα xS, Sα yS, xy⟩, xS, yS⟩,
  rintro ⟨⟨_, _, xy⟩, xS, yS⟩, exact ⟨xS, yS, xy⟩,
end

lemma inf_card_is_limit {κ : Set} (κcard : κ.is_cardinal) (κinf : ¬ κ.finite_cardinal) : κ.limit_ord :=
begin
  refine ⟨card_is_ord κcard, _, _⟩,
  { rw finite_cardinal_iff_nat at κinf, intro κz, subst κz, exact κinf zero_nat, },
  { rintro ⟨μ, κμ⟩, subst κμ,
    obtain ⟨κord, h⟩ := init_iff_card.mpr κcard,
    refine h ⟨_, self_mem_succ, _⟩,
    have μinf : ¬μ.card.finite_cardinal, rw finite_cardinal_iff_nat at κinf,
      intro μω, rw [card_finite_iff_finite, ord_finite (ord_of_succ_ord κord)] at μω,
      exact κinf (succ_nat_is_nat μω),
    rw [←card_equiv, card_succ_eq,
      card_add_comm card_is_card (nat_is_cardinal one_nat),
      card_add_eq_right_of_le (nat_is_cardinal one_nat) card_is_card μinf (nat_le_inf' one_nat card_is_card μinf)], },
end

lemma ord_finite_iff {α : Set} (αord : α.is_ordinal) : α.is_finite ↔ α ∈ ω :=
begin
  split,
    intro αfin, apply classical.by_contradiction, intro h,
    rw [ord_not_lt_iff_le αord omega_is_ord, ord_le_iff_sub omega_is_ord αord] at h,
    apply inf_of_sup_inf nat_infinite h αfin,
  exact nat_finite,
end

lemma exists_least_card_of_exists {p : Set → Prop} (h : ∃ κ : Set, κ.is_cardinal ∧ p κ) :
  ∃ κ : Set, κ.is_cardinal ∧ p κ ∧ ∀ {μ : Set}, μ.is_cardinal → p μ → κ ≤ μ :=
begin
  rcases h with ⟨κ, κcard, pκ⟩,
  obtain ⟨α, αord, ⟨αcard, pα⟩, h⟩ := @exists_least_ord_of_exists (λ α, α.is_cardinal ∧ p α) ⟨κ, card_is_ord κcard, κcard, pκ⟩,
  refine ⟨_, αcard, pα, _⟩, intros μ μcard pμ, exact h (card_is_ord μcard) ⟨μcard, pμ⟩,
end

def cofinal (γ S : Set) : Prop :=
S ⊆ γ ∧ γ = S.Union

lemma limit_cf_self {γ : Set} (γord : γ.limit_ord) : γ.cofinal γ :=
⟨subset_self, limit_ord_eq_Union γord⟩

lemma limit_cf_lemma {γ : Set} (γord : γ.limit_ord) : ∃ κ : Set, (∃ S : Set, γ.cofinal S ∧ S.card = κ) ∧
  ∀ {S : Set}, γ.cofinal S → κ ≤ S.card :=
begin
  obtain ⟨κ, -, h₁, h₂⟩ := @exists_least_card_of_exists (λ κ, ∃ S : Set, γ.cofinal S ∧ S.card = κ)
    ⟨_, card_is_card, _, ⟨subset_self, limit_ord_eq_Union γord⟩, rfl⟩,
  refine ⟨_, h₁, _⟩, intros S γS, exact h₂ card_is_card ⟨_, γS, rfl⟩,
end

local attribute [instance] classical.prop_decidable

noncomputable def cf (γ : Set) : Set :=
if ne : γ = ∅ then ∅
else if ex : ∃ α : Set, γ = α.succ then one
else if γord : γ.limit_ord then classical.some (limit_cf_lemma γord)
else ∅

lemma cf_zero : cf ∅ = ∅ :=
begin
  dsimp [cf], rw if_pos rfl,
end

lemma cf_succ {α : Set} : α.succ.cf = one :=
begin
  dsimp [cf], rw [if_neg succ_neq_empty, if_pos], exact ⟨_, rfl⟩,
end

lemma cf_limit {γ : Set} (γord : γ.limit_ord) : ∃ S : Set, γ.cofinal S ∧ S.card = γ.cf :=
begin
  dsimp [cf], rw [if_neg γord.ne, if_neg γord.ns, dif_pos γord],
  obtain ⟨h, -⟩ := classical.some_spec (limit_cf_lemma γord), exact h,
end

lemma cf_limit_least {γ : Set} (γord : γ.limit_ord) {S : Set} (γS : γ.cofinal S) : γ.cf ≤ S.card :=
begin
  dsimp [cf], rw [if_neg γord.ne, if_neg γord.ns, dif_pos γord],
  obtain ⟨-, h⟩ := classical.some_spec (limit_cf_lemma γord), exact h γS,
end

lemma cf_least {α : Set} (αord : α.is_ordinal) {S : Set} (αS : α.cofinal S) : α.cf ≤ S.card :=
begin
  rcases ord_cases αord with (αz|(⟨β, αβ⟩|αord')),
  { subst αz, rw cf_zero, exact empty_le_ord (card_is_ord card_is_card), },
  { subst αβ, rw cf_succ, apply card_ge_one_of_inhab,
    rcases αS with ⟨-, αS⟩,
    have βS : β ∈ S.Union, rw ←αS, exact self_mem_succ, rw mem_Union at βS,
    rcases βS with ⟨γ, γS, -⟩, exact ⟨_, γS⟩, },
  { exact cf_limit_least αord' αS, },
end

lemma cf_ord_le_card {α : Set} (αord : α.is_ordinal) : α.cf ≤ α.card :=
begin
  rcases ord_cases αord with (αz|(⟨β, αβ⟩|αord')),
  { subst αz, rw [cf_zero, card_empty], exact empty_le_ord αord, },
  { subst αβ,
    have βord : β.is_ordinal := ord_of_succ_ord αord,
    rw [cf_succ, ←card_le_iff_le (nat_is_cardinal one_nat) card_is_card, succ, card_add_spec rfl rfl (ord_disj βord), ←add_base one_nat,
      ←card_add_eq_ord_add (finite_cardinal_iff_nat.mpr one_nat) (finite_cardinal_iff_nat.mpr zero_nat),
    card_singleton], refine card_add_le_of_le_right (nat_is_cardinal zero_nat) card_is_card (zero_card_le card_is_card) (nat_is_cardinal one_nat), },
  { exact cf_limit_least αord' (limit_cf_self αord'), },
end

lemma cf_is_card {α : Set} (αord : α.is_ordinal) : α.cf.is_cardinal :=
begin
  rcases ord_cases αord with (αz|(⟨β, αβ⟩|αord')),
  { subst αz, rw [cf_zero], exact nat_is_cardinal zero_nat, },
  { subst αβ, rw [cf_succ], exact nat_is_cardinal one_nat, },
  { obtain ⟨S, -, Scard⟩ := cf_limit αord', rw ←Scard, exact card_is_card, },
end

lemma cf_card {κ : Set} (κcard : κ.is_cardinal) : κ.cf ≤ κ :=
begin
  nth_rewrite 1 ←card_of_cardinal_eq_self κcard,
  exact cf_ord_le_card (card_is_ord κcard),
end

lemma unbounded_nats_inf {S : Set} (Sω : S ⊆ ω) (Sin : S.inhab) (un : ∀ {n : Set}, n ∈ S → ∃ m : Set, m ∈ S ∧ n ∈ m) : ¬ S.is_finite :=
begin
  let R : struct := S.eps_order_struct,
  have Rwell : R.fld.well_order R.rel,
    have Re : R = S.struct_restrict (eps_order_struct ω) := struct_restrict_eq omega_is_ord Sω,
    rw Re, refine well_order_struct_restrict (ordinal_well_ordered' omega_is_ord) _, exact Sω,
  intro Sfin, rw [←card_finite_iff_finite, finite_cardinal_iff_nat] at Sfin,
  obtain ⟨α, αord, f, fcorr, iso⟩ := exists_iso_ord Rwell,
  have equin : α ≈ S := ⟨_, fcorr⟩,
  rw ←card_equiv at equin, rw [←equin, ←finite_cardinal_iff_nat, card_finite_iff_finite, ord_finite_iff αord] at Sfin,
  simp only [eps_order_struct_fld] at fcorr iso,
  rcases exists_pred Sfin with (αz|⟨m, mω, αm⟩),
    subst αz, suffices h : S = ∅, exact ne_empty_of_inhabited _ Sin h,
    rwa [←fcorr.onto.right.right, ←dom_ran_eq_empty_iff, fcorr.onto.right.left],
  subst αm,
  have fmS : f.fun_value m ∈ S, rw ←fcorr.onto.right.right, apply fun_value_def'' fcorr.onto.left,
    rw fcorr.onto.right.left, exact self_mem_succ,
  obtain ⟨n, nS, mn⟩ := un fmS, rw [←fcorr.onto.right.right, mem_ran_iff fcorr.onto.left] at nS,
  obtain ⟨k, km, nfk⟩ := nS, rw fcorr.onto.right.left at km, subst nfk,
  specialize iso self_mem_succ km,
  have fkS : f.fun_value k ∈ S, rw ←fcorr.onto.right.right, apply fun_value_def'' fcorr.onto.left,
    rwa fcorr.onto.right.left,
  simp only [pair_mem_eps_order self_mem_succ km, R, pair_mem_eps_order fmS fkS] at iso,
  exact succ_imm m ⟨_, iso.mpr mn, km⟩,
end

lemma unbounded_ords_inf {α : Set} (αord : α.is_ordinal) {S : Set} (Sα : S ⊆ α) (Sin : S.inhab) (un : ∀ {n : Set}, n ∈ S → ∃ m : Set, m ∈ S ∧ n ∈ m) : ¬ S.is_finite :=
begin
  let R : struct := S.eps_order_struct,
  have Rwell : R.fld.well_order R.rel,
    have Re : R = S.struct_restrict (eps_order_struct α) := struct_restrict_eq αord Sα,
    rw Re, refine well_order_struct_restrict (ordinal_well_ordered' αord) _, exact Sα,
  intro Sfin, rw [←card_finite_iff_finite, finite_cardinal_iff_nat] at Sfin,
  obtain ⟨α, αord, f, fcorr, iso⟩ := exists_iso_ord Rwell,
  have equin : α ≈ S := ⟨_, fcorr⟩,
  rw ←card_equiv at equin, rw [←equin, ←finite_cardinal_iff_nat, card_finite_iff_finite, ord_finite_iff αord] at Sfin,
  simp only [eps_order_struct_fld] at fcorr iso,
  rcases exists_pred Sfin with (αz|⟨m, mω, αm⟩),
    subst αz, suffices h : S = ∅, exact ne_empty_of_inhabited _ Sin h,
    rwa [←fcorr.onto.right.right, ←dom_ran_eq_empty_iff, fcorr.onto.right.left],
  subst αm,
  have fmS : f.fun_value m ∈ S, rw ←fcorr.onto.right.right, apply fun_value_def'' fcorr.onto.left,
    rw fcorr.onto.right.left, exact self_mem_succ,
  obtain ⟨n, nS, mn⟩ := un fmS, rw [←fcorr.onto.right.right, mem_ran_iff fcorr.onto.left] at nS,
  obtain ⟨k, km, nfk⟩ := nS, rw fcorr.onto.right.left at km, subst nfk,
  specialize iso self_mem_succ km,
  have fkS : f.fun_value k ∈ S, rw ←fcorr.onto.right.right, apply fun_value_def'' fcorr.onto.left,
    rwa fcorr.onto.right.left,
  simp only [pair_mem_eps_order self_mem_succ km, R, pair_mem_eps_order fmS fkS] at iso,
  exact succ_imm m ⟨_, iso.mpr mn, km⟩,
end

lemma Union_finite_nats_finite {S : Set} (Sfin : S.is_finite) (Sω : S ⊆ ω)
  (unb : ∀ {n : Set}, n ∈ S → (∃ (m : Set), m ∈ S ∧ n ∈ m)) : S.Union.is_finite :=
begin
  by_cases Sin : S.inhab,
    apply classical.by_contradiction, intro h,
    have he : S.Union = ω, refine eq_nat_of_induct_sub _ (Union_sub (λ n nS, subset_nat_of_mem_nat (Sω nS))),
      split; simp only [mem_Union, exists_prop],
        rcases Sin with ⟨n, nS⟩, obtain ⟨m, mS, nm⟩ := unb nS,
        exact ⟨_, mS, nat_pos_of_not_empty nm (Sω mS)⟩,
      rintros n ⟨m, mS, nm⟩, obtain ⟨k, kS, mk⟩ := unb mS,
      refine ⟨_, kS, nat_lt_of_le_of_lt (le_of_not_lt (Sω mS) (succ_nat_is_nat (mem_nat_of_mem_nat_of_mem (Sω mS) nm)) _) mk (Sω kS)⟩,
      intro mn, exact succ_imm n ⟨_, nm, mn⟩,
    apply @unbounded_nats_inf S Sω _ @unb Sfin,
    have zn := zero_nat, rw [←he, mem_Union] at zn, rcases zn with ⟨m, mS, -⟩,
    exact ⟨_, mS⟩,
  have Se : S = ∅ := classical.by_contradiction (λ h, Sin (inhabited_of_ne_empty h)),
  subst Se, rw Union_empty, exact nat_finite zero_nat,
end

lemma cf_omega_eq : cf ω = card ω :=
begin
  cases cf_ord_le_card omega_is_ord,
    obtain ⟨S, ⟨h₁, h₂⟩, Scard⟩ := cf_limit omega_limit_ord,
    exfalso, apply nat_infinite, rw h₂, apply Union_finite_nats_finite,
        rw [←card_finite_iff_finite, Scard, finite_cardinal_iff_nat],
        nth_rewrite 1 ←card_of_cardinal_eq_self omega_is_card, exact h,
      have zn := zero_nat, rw [h₂, mem_Union] at zn,
      rcases zn with ⟨x, xS, -⟩, exact h₁,
    intros n nS, specialize h₁ nS, rw h₂ at h₁,
    simp only [mem_Union, exists_prop] at h₁, exact h₁,
  exact h,
end

def regular (κ : Set) : Prop := κ.cf = κ
def singular (κ : Set) : Prop := κ.cf.card_lt κ

lemma sing_or_reg {κ : Set} (κcard : κ.is_cardinal) : κ.regular ∨ κ.singular :=
or.elim (cf_card κcard)
  (λ h, or.inr (card_lt_of_mem (cf_is_card (card_is_ord κcard)) κcard h))
  (λ h, or.inl h)

lemma cf_spec {α : Set} (αord : α.is_ordinal) : ∃ S : Set, S ⊆ α ∧ S.card = α.cf ∧ ∀ {β : Set}, β.is_ordinal → S ⊆ β → α ≤ β :=
begin
  rcases ord_cases αord with (αz|(⟨γ, αγ⟩|αord')),
  { subst αz, rw cf_zero, refine ⟨_, subset_self, _, λ β βord Sβ, empty_le_ord βord⟩,
    rw card_nat zero_nat, },
  { subst αγ, refine ⟨{γ}, _, _, _⟩,
    { intros γ' γγ, rw mem_singleton at γγ, subst γγ, exact self_mem_succ, },
    { rw [card_singleton, cf_succ], },
    { intros β βord γβ, apply succ_least_upper_bound βord, apply γβ,
      rw mem_singleton, }, },
  { obtain ⟨S, ⟨Sα, h⟩, Scard⟩ := cf_limit αord', subst h,
    refine ⟨_, Sα, Scard, λ β βord Sβ, _⟩, rw ←ord_not_lt_iff_le βord αord,
    intros βS, rw mem_Union at βS, rcases βS with ⟨γ, γS, βγ⟩,
    exact ord_mem_irrefl βord (ord_mem_trans βord βγ (Sβ γS)), },
end

lemma cf_least' {α : Set} (αord : α.is_ordinal) {S : Set} (Sα : S ⊆ α) (h : ∀ {β : Set}, β.is_ordinal → S ⊆ β → α ≤ β) : α.cf ≤ S.card :=
begin
  rcases ord_cases αord with (αz|(⟨γ, αγ⟩|αord')),
  { subst αz, rw cf_zero, exact empty_le_ord (card_is_ord card_is_card), },
  { subst αγ, rw cf_succ,
    have Sin : S.inhab, apply inhabited_of_ne_empty, intro Se, subst Se,
      specialize h zero_is_ord subset_self, exact not_succ_le_empty h,
    exact card_ge_one_of_inhab Sin, },
  { have αS : α = S.Union, rw eq_iff_subset_and_subset, split,
        intros β βα, simp only [mem_Union, exists_prop], apply classical.by_contradiction, intro h',
        push_neg at h', replace h' : S ⊆ β.succ :=
          λ γ γS, mem_succ_iff_le.mpr ((ord_not_lt_iff_le (ord_of_mem_ord αord βα) (ord_of_mem_ord αord (Sα γS))).mp (h' _ γS)),
        refine succ_imm β ⟨_, βα, _⟩, specialize h (succ_ord_of_ord (ord_of_mem_ord αord βα)) h', cases h,
          exact h,
        exfalso, exact αord'.ns ⟨_, h⟩,
      exact subset_trans (Union_sub_of_sub Sα) (ordinal_trans αord),
    exact cf_least αord ⟨Sα, αS⟩, },
end

lemma regular_iff_ne {κ : Set} (κcard : κ.is_cardinal) (κinf : ¬ κ.finite_cardinal) : κ.regular ↔ ∀ {S : Set}, κ.cofinal S → S.card = κ :=
begin
  split,
    intro reg, intros S κS, cases cf_least (card_is_ord κcard) κS,
      exfalso, apply @not_mem_self S.card, refine ord_mem_trans (card_is_ord card_is_card) _ h,
      dsimp [regular] at reg, rw [reg, ←card_lt_iff_mem card_is_card κcard], split,
        rcases κS with ⟨κS, -⟩,
        rw ←card_of_cardinal_eq_self κcard, exact card_le_of_subset κS,
      symmetry, apply ne_of_mem, rwa ←reg,
    dsimp [regular] at reg, rw [←reg, h],
  intro h, dsimp [regular], cases cf_card κcard with h₁ h₁,
    exfalso, apply @not_mem_self κ, obtain ⟨S, cof, Scard⟩ := cf_limit (inf_card_is_limit κcard κinf),
    rwa [←Scard, h cof] at h₁,
  exact h₁,
end

-- chapter 6, exercise 26
theorem ch6_26 {κ : Set.{u}} (κcard : κ.is_cardinal) : ∀ {A : Set.{u}}, (∀ {x : Set}, x ∈ A → x.card.card_le κ) → A.Union.card.card_le (A.card.card_mul κ) :=
begin
  rcases κcard with ⟨K, Kcard⟩, subst Kcard,
  have h₁ : ∀ {A : Set.{u}}, ∅ ∉ A → (∀ {x : Set}, x ∈ A → x.card.card_le K.card) → A.Union.card.card_le (A.card.card_mul K.card),
    intros A h₁ hA,
    by_cases Ain : A.inhab,
      let H := pair_sep_eq A (into_funs K A.Union).powerset (λ y, {g ∈ into_funs K y | g.onto_fun K y}),
      have Hfun : H.is_function := pair_sep_eq_is_fun,
      have Hdom : H.dom = A, apply pair_sep_eq_dom_eq, dsimp, intros x xA, rw mem_powerset,
        intros g hg, rw mem_sep at hg, rw mem_into_funs, refine into_of_into_ran_sub _ (into_of_onto hg.right),
        exact subset_Union_of_mem xA,
      have hH : ∀ x : Set, x ∈ A → H.fun_value x ≠ ∅, intros x xA,
        specialize hA xA, rw card_le_iff_equin' at hA,
        have xin : x ≠ ∅, intro xe, subst xe, exact h₁ xA,
        replace xin := inhabited_of_ne_empty xin,
        obtain ⟨g, gonto⟩ := exists_onto_of_dominated xin hA,
        rw ←Hdom at xA, rw pair_sep_eq_fun_value xA, dsimp, apply ne_empty_of_inhabited,
        use g, rw [mem_sep, mem_into_funs], exact ⟨into_of_onto gonto, gonto⟩,
      have memHm : ∀ {x : Set}, x ∈ A → ∀ {g : Set}, g ∈ H.fun_value x ↔ g.onto_fun K x,
        intros m mω g, rw ←Hdom at mω, rw pair_sep_eq_fun_value mω, dsimp, rw [mem_sep, mem_into_funs], split,
          rintro ⟨-, h⟩, exact h,
        intro h, exact ⟨into_of_onto h, h⟩,
      obtain ⟨F, Ffun, Fdom, hF⟩ := ax_ch_2 ⟨Hfun, Hdom, hH⟩,
      let f := pair_sep_eq (prod A K) A.Union (λ z, (F.fun_value z.fst).fun_value z.snd),
      have fonto : f.onto_fun (prod A K) A.Union, refine ⟨pair_sep_eq_is_fun, pair_sep_eq_dom_eq _, pair_sep_eq_ran_eq _⟩; dsimp,
          simp only [mem_prod, mem_Union, exists_prop], rintros z ⟨x, xA, y, yK, zxy⟩, subst zxy, rw [fst_congr, snd_congr],
          have h := (memHm xA).mp (hF _ xA),
          refine ⟨_, xA, _⟩,
          nth_rewrite 1 ←h.right.right, apply fun_value_def'' h.left, rw h.right.left, exact yK,
        simp only [mem_Union, exists_prop], rintros y ⟨B, BA, yB⟩,
        specialize hF _ BA, rw memHm BA at hF,
        rw [←hF.right.right, mem_ran_iff hF.left] at yB, rcases yB with ⟨x, xK, xe⟩, subst xe,
        rw hF.right.left at xK, use B.pair x, simp only [pair_mem_prod, fst_congr, snd_congr],
        exact ⟨⟨BA, xK⟩, rfl⟩,
      have Ain' : A.Union.inhab, rcases Ain with ⟨B, BA⟩,
        have Bin : B.inhab := classical.by_contradiction (λ Bnin,
          have Bne : B = ∅ := classical.by_contradiction (λ Bne, Bnin (inhabited_of_ne_empty Bne)),
          h₁ (Bne ▸ BA)),
        rcases Bin with ⟨x, xB⟩, use x, rw mem_Union, exact ⟨_, BA, xB⟩,
      rw [←card_mul_spec rfl rfl, card_le_iff_equin'], exact dominates_of_onto_fun ⟨f, fonto⟩,
    have h : A = ∅ := classical.by_contradiction (λ Ane, Ain (inhabited_of_ne_empty Ane)),
    subst h, rw union_empty_eq_empty, nth_rewrite 0 card_nat zero_nat,
    exact zero_card_le (mul_cardinal card_is_card card_is_card),
  intros A hA, rw Union_diff_empty_eq,
  apply @card_le_trans _ ((A \ {∅}).card.card_mul K.card) (mul_cardinal card_is_card card_is_card),
    apply h₁,
      intro h, rw [mem_diff, mem_singleton] at h, exact h.right rfl,
    intros x hx, exact hA (subset_diff hx),
  refine card_mul_le_of_le_left card_is_card card_is_card _ card_is_card, exact card_le_of_subset subset_diff,
end

-- Theorem 9M
theorem Aleph_succ_regular {α : Set} (αord : α.is_ordinal) : α.succ.Aleph.regular :=
begin
  have αord' := succ_ord_of_ord αord,
  rw regular_iff_ne (Aleph_is_card αord') (Aleph_inf αord'),
  rintros S ⟨Sα, αS⟩,
  have h : ∀ (β : Set), β ∈ S → β.card.card_le α.Aleph,
  { intros β βS, rw ←card_not_lt_iff_le (Aleph_is_card αord) card_is_card,
    intros αβ, specialize Sα βS,
    have βα : β.card.card_le α.succ.Aleph.card := card_le_of_ord_mem (card_is_ord (Aleph_is_card αord')) Sα,
    rw card_le_iff at βα, cases βα, rotate,
      rw card_equiv at βα,
      exact (init_iff_card.mpr (Aleph_is_card αord')).right ⟨_, Sα, equin_symm βα⟩,
    rw card_of_cardinal_eq_self (Aleph_is_card αord') at βα,
    apply Aleph_imm αord ⟨_, card_is_card, αβ, βα⟩, },
  replace h := ch6_26 (Aleph_is_card αord) h, apply card_eq_of_le_of_le card_is_card (Aleph_is_card αord'),
    rw ←card_of_cardinal_eq_self (Aleph_is_card αord'), exact card_le_of_subset Sα,
  rw ←card_not_lt_iff_le card_is_card (Aleph_is_card αord'), intro Sα,
  replace Sα := Aleph_le_of_lt_succ αord card_is_card Sα,
  have h₁ : α.succ.Aleph.card_le α.Aleph,
    rw [←card_of_cardinal_eq_self (Aleph_is_card αord'), αS],
    apply card_le_trans (mul_cardinal card_is_card (Aleph_is_card αord)) h,
    nth_rewrite 1 ←mul_infinite_card_eq_self (Aleph_is_card αord) (Aleph_inf αord),
    apply card_mul_le_of_le_left card_is_card (Aleph_is_card αord) Sα (Aleph_is_card αord),
  rw ←card_not_lt_iff_le (Aleph_is_card αord) (Aleph_is_card αord') at h₁,
  exact h₁ (Aleph_lt_of_mem αord' self_mem_succ),
end

lemma cf_le_of {γ : Set} (γord : γ.is_ordinal) {κ : Set} (κcard : κ.is_cardinal)
  {S : Set} (γS : γ.cofinal S) (cardS : S.card.card_le κ) : γ.cf.card_le κ :=
begin
  refine card_le_trans card_is_card _ cardS, rw card_le_iff_le (cf_is_card γord) card_is_card,
  exact cf_least γord γS,
end

lemma cf_pred {p : Set → Prop} {γ : Set} (γord : γ.limit_ord)
  (h : ∀ {S : Set}, γ.cofinal S → p S.card) : p γ.cf :=
begin
  obtain ⟨S, γS, cardS⟩ := cf_limit γord, rw ←cardS, exact h γS,
end

-- Theorem 9N
theorem cf_Aleph_limit {γ : Set} (γord : γ.limit_ord) : γ.Aleph.cf = γ.cf :=
begin
  have Aord : γ.Aleph.is_ordinal := card_is_ord (Aleph_is_card γord.ord),
  apply card_eq_of_le_of_le (cf_is_card Aord) (cf_is_card γord.ord),
  { obtain ⟨S, ⟨Sγ, γS⟩, Scard⟩ := cf_limit γord,
    have sub : repl_img Aleph S ⊆ γ.Aleph, intros A hA,
      rw mem_repl_img at hA, rcases hA with ⟨α, αS, he⟩, subst he,
      rw ←card_lt_iff_mem (Aleph_is_card (ord_of_mem_ord γord.ord (Sγ αS))) (Aleph_is_card γord.ord),
      apply Aleph_lt_of_mem γord.ord (Sγ αS),
    have hc : γ.Aleph = (repl_img Aleph S).Union, rw γS,
      change S.sup.Aleph = (repl_img Aleph S).sup,
      refine sup_norm_fun Aleph_ord_op Aleph_normal _ (λ α αS, ord_of_mem_ord γord.ord (Sγ αS)),
      refine ne_empty_of_inhabited _ (inhab_of_Union_inhab _),
      rw ←γS, exact ⟨_, limit_ord_pos γord⟩,
    apply cf_le_of Aord (cf_is_card γord.ord) ⟨sub, hc⟩,
    rw ←Scard, exact repl_img_card_le, },
  { apply cf_pred (inf_card_is_limit (Aleph_is_card γord.ord) (Aleph_inf γord.ord)),
    rintros A ⟨γA, Aγ⟩,
    let B : Set := {β ∈ γ | ∃ α : Set, α ∈ A ∧ β.Aleph = α.card},
    have Bords : ∀ ⦃β : Set⦄, β ∈ B → β.is_ordinal,
      intros β βB, rw mem_sep at βB, exact ord_of_mem_ord γord.ord βB.left,
    have h : ∀ {α : Set}, α ∈ A → ω ≤ α → ∃ β : Set, β ∈ γ ∧ β.Aleph = α.card,
      intros α αA ωα,
      have γA' := γA αA,
      simp only [Aleph_limit_ord_eq γord, mem_Union, exists_prop, mem_repl_img] at γA',
      rcases γA' with ⟨βA, ⟨β, βγ, he⟩, αβ⟩, subst he,
      have h := Aleph_is_card (ord_of_mem_ord γord.ord βγ),
      replace αβ := card_le_of_ord_mem (card_is_ord h) αβ,
      rw card_of_cardinal_eq_self h at αβ,
      have αinf : ¬ α.card.finite_cardinal, rw [card_finite_iff_finite], intro αfin,
        have αord := ord_of_mem_ord Aord (γA αA),
        rw ord_finite αord at αfin,
        exact ord_mem_irrefl αord (ord_lt_of_lt_of_le αord αfin ωα),
      obtain ⟨δ, δord, αδ⟩ := inf_card_eq_Aleph card_is_card αinf,
      rw [αδ, Aleph_le_of_le δord (ord_of_mem_ord γord.ord βγ)] at αβ,
      exact ⟨_, ord_lt_of_le_of_lt γord.ord αβ βγ, αδ.symm⟩,
    have hzA : Aleph ∅ ∈ A.Union,
      have hoA : one.Aleph ⊆ A.Union, rw [←Aγ, Aleph_limit_ord_eq γord],
        apply subset_Union_of_mem, rw mem_repl_img, refine ⟨_, succ_mem_limit γord (limit_ord_pos γord), rfl⟩,
      apply hoA, rw ←card_lt_iff_mem (Aleph_is_card zero_is_ord) (Aleph_is_card one_is_ord),
      exact Aleph_lt_of_mem one_is_ord zero_lt_one,
    have Bin : B.inhab, rw mem_Union at hzA, rcases hzA with ⟨α, αA, zα⟩,
      rw [Aleph_zero_eq, card_of_cardinal_eq_self omega_is_card] at zα,
      obtain ⟨β, βγ, βα⟩ := h αA (or.inl zα),
      use β, rw mem_sep, exact ⟨βγ, _, αA, βα⟩,
    obtain ⟨C, CB⟩ := Bin,
    have BA : B.card.card_le A.card, rw card_le_iff_equin', apply dominates_of_onto_fun,
      let f : Set := pair_sep_eq A B (λ α, if αA : α ∈ A then if ωα : ω ≤ α then classical.some (h αA ωα) else C else ∅),
      refine ⟨f, pair_sep_eq_is_fun, pair_sep_eq_dom_eq _, pair_sep_eq_ran_eq _⟩,
      { intros α αA, dsimp, rw [dif_pos αA], by_cases ωα : ω ≤ α,
          rw dif_pos ωα, obtain ⟨βγ, βα⟩ := classical.some_spec (h αA ωα),
          rw mem_sep, exact ⟨βγ, _, αA, βα⟩,
        rwa dif_neg ωα, },
      { intros β βB, rw mem_sep at βB, rcases βB with ⟨βγ, α, αA, βα⟩, refine ⟨_, αA, _⟩,
        dsimp, rw dif_pos αA,
        have αord : α.is_ordinal := ord_of_mem_ord (card_is_ord (Aleph_is_card γord.ord)) (γA αA),
        have ωα : ω ≤ α, rw [←ord_not_lt_iff_le αord omega_is_ord, ←ord_finite_iff αord,
          ←card_finite_iff_finite, ←βα], exact Aleph_inf (ord_of_mem_ord γord.ord βγ),
        rw dif_pos ωα, obtain ⟨fαγ, fαα⟩ := classical.some_spec (h αA ωα),
        apply Aleph_oto'' (ord_of_mem_ord γord.ord βγ) (ord_of_mem_ord γord.ord fαγ),
        rw [βα, fαα], },
    refine card_le_trans card_is_card _ BA,
    refine cf_le_of γord.ord card_is_card ⟨sep_subset, _⟩ card_le_refl,
    have h₁ : ∀ {α : Set}, α ∈ A → α.card.card_le B.Union.Aleph.card,
      intros α αA, by_cases ωα : ω ≤ α,
      { obtain ⟨β, βγ, βα⟩ := h αA ωα,
        rw [←βα, ←card_of_cardinal_eq_self (Aleph_is_card (ord_of_mem_ord γord.ord βγ))],
        apply card_le_of_subset,
        have h' : B.Union.Aleph = (repl_img Aleph B).Union,
          refine sup_norm_fun Aleph_ord_op Aleph_normal _ _,
            apply ne_empty_of_inhabited,
            use β, rw mem_sep, exact ⟨βγ, _, αA, βα⟩,
          intros β βB, rw mem_sep at βB, exact ord_of_mem_ord γord.ord βB.left,
        rw h', apply subset_Union_of_mem, rw mem_repl_img, refine ⟨_, _, rfl⟩, rw mem_sep,
        exact ⟨βγ, _, αA, βα⟩, },
      { have hzA : Aleph ∅ ∈ A.Union,
          have hoA : one.Aleph ⊆ A.Union, rw [←Aγ, Aleph_limit_ord_eq γord],
            apply subset_Union_of_mem, rw mem_repl_img, refine ⟨_, succ_mem_limit γord (limit_ord_pos γord), rfl⟩,
          apply hoA, rw ←card_lt_iff_mem (Aleph_is_card zero_is_ord) (Aleph_is_card one_is_ord),
          exact Aleph_lt_of_mem one_is_ord zero_lt_one,
        rw mem_Union at hzA, rcases hzA with ⟨μ, μA, zμ⟩,
        have μB := γA μA, simp only [Aleph_limit_ord_eq γord, mem_Union, exists_prop, mem_repl_img] at μB,
        rcases μB with ⟨e, ⟨β, βγ, he⟩, μβ⟩, subst he,
        have μord : μ.is_ordinal := ord_of_mem_ord (card_is_ord (Aleph_is_card γord.ord)) (γA μA),
        have μinf : ¬ μ.is_finite, rw [ord_finite_iff μord, ord_not_lt_iff_le μord omega_is_ord,
          ←card_of_cardinal_eq_self omega_is_card, ←Aleph_zero_eq], left, exact zμ,
        rw ←card_finite_iff_finite at μinf,
        obtain ⟨δ, δord, μδ⟩ := inf_card_eq_Aleph card_is_card μinf,
        have αord : α.is_ordinal := ord_of_mem_ord (card_is_ord (Aleph_is_card γord.ord)) (γA αA),
        rw ord_not_le_iff_lt omega_is_ord αord at ωα,
        apply card_le_trans (Aleph_is_card zero_is_ord),
          rw Aleph_zero_eq, exact card_le_of_ord_mem omega_is_ord ωα,
        apply card_le_trans (Aleph_is_card δord),
          rw Aleph_le_of_le zero_is_ord δord, exact empty_le_ord δord,
        rw ←card_of_cardinal_eq_self (Aleph_is_card δord), apply card_le_of_subset,
        have βord := ord_of_mem_ord γord.ord βγ,
        have δγ : δ ∈ γ, refine ord_lt_of_le_of_lt γord.ord _ βγ, rw ←Aleph_le_of_le δord βord,
          rw [←μδ, ←card_of_cardinal_eq_self (Aleph_is_card βord)],
          exact card_le_of_ord_mem (card_is_ord (Aleph_is_card βord)) μβ,
        have h' : B.Union.Aleph = (repl_img Aleph B).Union,
          refine sup_norm_fun Aleph_ord_op Aleph_normal _ _,
            apply ne_empty_of_inhabited,
            use δ, rw mem_sep, exact ⟨δγ, _, μA, μδ.symm⟩,
          intros β βB, rw mem_sep at βB, exact ord_of_mem_ord γord.ord βB.left,
        rw h', apply subset_Union_of_mem, rw mem_repl_img, refine ⟨_, _, rfl⟩, rw mem_sep,
        exact ⟨δγ, _, μA, μδ.symm⟩, },
    have γB : γ ≤ B.Union.succ,
      have Asub : A ⊆ B.Union.succ.Aleph, intros α αA,
        have αord : α.is_ordinal := ord_of_mem_ord (card_is_ord (Aleph_is_card γord.ord)) (γA αA),
        rw ←ord_not_le_iff_lt (card_is_ord (Aleph_is_card (succ_ord_of_ord (Union_ords_is_ord Bords)))) αord,
        intro h₂, replace h₂ := card_le_of_ord_le αord h₂,
        suffices h₃ : ¬ B.Union.Aleph.card_lt B.Union.succ.Aleph,
          exact h₃ (Aleph_lt_of_mem (succ_ord_of_ord (Union_ords_is_ord Bords)) self_mem_succ),
        rw [←card_of_cardinal_eq_self (Aleph_is_card (Union_ords_is_ord Bords)),
          ←card_of_cardinal_eq_self (Aleph_is_card (succ_ord_of_ord (Union_ords_is_ord Bords))),
          card_not_lt_iff_le card_is_card card_is_card],
        apply card_le_trans card_is_card h₂ (h₁ αA),
      rw [←Aleph_le_of_le γord.ord (succ_ord_of_ord (Union_ords_is_ord Bords)),
        card_le_iff_le (Aleph_is_card γord.ord) (Aleph_is_card (succ_ord_of_ord (Union_ords_is_ord Bords))),
        ord_le_iff_sub (card_is_ord (Aleph_is_card γord.ord)) (card_is_ord (Aleph_is_card (succ_ord_of_ord (Union_ords_is_ord Bords)))),
        Aγ],
      intro δ, rw [mem_Union], rintro ⟨α, αA, δα⟩,
      exact ord_mem_trans (card_is_ord (Aleph_is_card (succ_ord_of_ord (Union_ords_is_ord Bords)))) δα (Asub αA),
    cases γB, rotate,
      exfalso, exact γord.ns ⟨_, γB⟩,
    rw mem_succ_iff_le at γB, cases γB,
      simp only [mem_Union, exists_prop, mem_sep] at γB, rcases γB with ⟨β, ⟨βγ, -⟩, γβ⟩,
      exfalso, exact no_2_cyle ⟨γβ, βγ⟩,
    assumption, },
end

theorem Aleph_omega_singular : (Aleph ω).singular :=
begin
  dsimp [singular], rw [cf_Aleph_limit omega_limit_ord, cf_omega_eq],
  apply card_lt_of_mem card_is_card (Aleph_is_card omega_is_ord),
  simp only [Aleph_limit_ord_eq omega_limit_ord, ←Aleph_zero_eq, mem_Union, exists_prop, mem_repl_img],
  refine ⟨_, ⟨_, one_nat, rfl⟩, _⟩, rw ←card_lt_iff_mem (Aleph_is_card zero_is_ord) (Aleph_is_card one_is_ord),
  exact Aleph_lt_of_mem one_is_ord zero_lt_one,
end

structure inaccessible (κ : Set) : Prop :=
(a : (Aleph ∅).card_lt κ)
(b : ∀ {μ : Set}, μ.is_cardinal → μ.card_lt κ → (two.card_exp μ).card_lt κ)
(c : κ.regular)

lemma diff_fun {F : Set} (Ffun : F.is_function) {X : Set} : (F \ X).is_function :=
begin
  rw is_function_iff at Ffun ⊢, refine ⟨diff_is_rel Ffun.left, λ x y y' xy xy', _⟩,
  rw mem_diff at xy xy', exact Ffun.right _ _ _ xy.left xy'.left,
end

lemma dom_diff {F X : Set} : (F \ X).dom ⊆ F.dom :=
begin
  intro x, simp only [mem_dom, mem_diff], rintro ⟨y, xy, -⟩, exact ⟨_, xy⟩,
end

lemma ord_of_sub_ord {α : Set} (αord : α.is_ordinal) {β : Set} (βα : β ⊆ α) (βtrans : β.transitive_set) : β.is_ordinal :=
begin
  rw is_ordinal_iff, refine ⟨βtrans, _⟩,
  have h := well_order_struct_restrict (ordinal_well_ordered' αord) βα,
  have h' : α.eps_order ∩ β.prod β = β.eps_order, apply rel_ext (inter_rel_is_rel pair_sep_is_rel) pair_sep_is_rel,
    simp only [pair_mem_pair_sep, mem_inter, pair_mem_prod], intros x y, split,
      rintro ⟨⟨-, -, xy⟩, xβ, yβ⟩, exact ⟨xβ, yβ, xy⟩,
    rintro ⟨xβ, yβ, xy⟩, exact ⟨⟨βα xβ, βα yβ, xy⟩, xβ, yβ⟩,
  rwa [struct_restrict_fld, struct_restrict_rel, eps_order_struct_rel, h'] at h,
end

-- Lemma 9P
lemma exists_sub_ord_seq {f : Set.{u}} (ffun : f.is_function) (fdom : f.dom.is_ordinal)
  (ford : ∀ {δ : Set}, δ ∈ f.ran → δ.is_ordinal) :
  ∃ g : Set, g.is_function ∧ g.dom.is_ordinal ∧ g.dom ≤ f.dom ∧ (∀ {δ : Set}, δ ∈ g.ran → δ.is_ordinal)
  ∧ (∀ {η : Set}, η ∈ g.dom → ∀ {ξ : Set}, ξ ∈ η → g.fun_value ξ ∈ g.fun_value η)
  ∧ g.ran ⊆ f.ran
  ∧ f.ran.Union = g.ran.Union :=
begin
  let P : Set → Set → Prop := λ g γ : Set, γ ∈ f.dom ∧ ∀ {δ : Set}, δ ∈ g.dom → f.fun_value (g.fun_value δ) ∈ f.fun_value γ,
  have h₁ : ∀ {g : Set}, (∃ γ : Set, P g γ) → ∃ γ : Set, γ.is_ordinal ∧ P g γ :=
    λ g ex, exists.elim ex (λ γ h, ⟨_, ord_of_mem_ord fdom h.left, h⟩),
  let F' : Set → Set := λ g, if ex : ∃ γ : Set, P g γ then classical.some (exists_least_ord_of_exists (h₁ ex)) else f.dom,
  let F := trans_rec f.dom f.dom.eps_order F',
  have Ffun : F.is_function := trans_rec_fun (ordinal_well_ordered fdom),
  have Fdom : F.dom = f.dom := trans_rec_dom (ordinal_well_ordered fdom),
  have Fspec : ∀ ⦃β : Set⦄, β ∈ f.dom → F.fun_value β = F' (F.restrict β),
    intros β hβ, nth_rewrite 1 ←seg_ord fdom hβ, exact trans_rec_spec (ordinal_well_ordered fdom) hβ,
  let Q : Set → Set → Prop := λ β γ : Set.{u}, γ ∈ f.dom ∧ ∀ {δ : Set}, δ ∈ β → f.fun_value (F.fun_value δ) ∈ f.fun_value γ,
  have Fval : ∀ {β : Set.{u}}, β ∈ f.dom → ¬ (∃ γ : Set, Q β γ) → F.fun_value β = f.dom,
  { intros β hβ h,
    have h' : ¬ ∃ γ : Set, P (F.restrict β) γ,
      rintro ⟨γ, hγ, h'⟩, refine h ⟨_, hγ, λ δ δβ, _⟩,
      have βf : β ⊆ f.dom, rw ←ord_le_iff_sub (ord_of_mem_ord fdom hβ) fdom, left, exact hβ,
      rw ←Fdom at hγ βf, rw ←restrict_fun_value Ffun βf δβ, rw ←restrict_dom βf at δβ,
      exact h' δβ,
    simp only [Fspec hβ, F', P, dif_neg h'], },
  have Fval' : ∀ {β : Set.{u}}, β ∈ f.dom → (∃ γ : Set, Q β γ) → Q β (F.fun_value β) ∧ ∀ {α : Set}, Q β α → F.fun_value β ≤ α,
  { intros β hβ h,
    have βf : β ⊆ f.dom, rw ←ord_le_iff_sub (ord_of_mem_ord fdom hβ) fdom, left, exact hβ,
    rw ←Fdom at βf,
    have h' : ∃ γ : Set, P (F.restrict β) γ,
      rcases h with ⟨γ, hγ, h'⟩, refine ⟨_, hγ, λ δ δβ, _⟩,
      rw restrict_dom βf at δβ, rw restrict_fun_value Ffun βf δβ,
      exact h' δβ,
    obtain ⟨-, ⟨hP, hP'⟩, hle⟩ := classical.some_spec (exists_least_ord_of_exists (h₁ h')),
    simp only [Fspec hβ, F', dif_pos h'], refine ⟨⟨hP, _⟩, _⟩,
      rw restrict_dom βf at hP', intros δ δβ, rw ←restrict_fun_value Ffun βf δβ, exact hP' δβ,
    rintros α ⟨hα, h⟩, apply hle (ord_of_mem_ord fdom hα), dsimp [P], rw restrict_dom βf, refine ⟨hα, λ δ δβ, _⟩,
    rw restrict_fun_value Ffun βf δβ, exact h δβ, },
  let C : Set := {β ∈ f.dom | ∃ γ : Set, Q β γ},
  let h := F.restrict C,
  have hfun : h.is_function := restrict_is_function Ffun,
  have hdom' : h.dom = C,
    have C' : C = {β ∈ F.dom | ∃ γ : Set, Q β γ}, rw Fdom,
    simp only [h, C', restrict_dom sep_subset],
  have hdom : h.dom ⊆ f.dom,
    rw hdom', exact sep_subset,
  have hspec : ∀ {β : Set}, β ∈ h.dom → h.fun_value β = F.fun_value β,
    intros β hβ, rw [hdom', ←Fdom] at hdom, rw hdom' at hβ, simp only [h, restrict_fun_value Ffun hdom hβ],
  let R : Set → Set → Prop := λ β γ : Set.{u}, γ ∈ f.dom ∧ ∀ {δ : Set}, δ ∈ β → f.fun_value (h.fun_value δ) ∈ f.fun_value γ,
  have h₂ : ∀ {β : Set}, β ∈ h.dom ↔ β ∈ f.dom ∧ ∃ γ : Set, Q β γ,
    intros β, rw [hdom', mem_sep],
  have h₃ : ∀ {β : Set}, β ∈ h.dom → h.fun_value β ∈ f.dom,
    intros β hβ,
    obtain ⟨hβ', ex⟩ := h₂.mp hβ,
    obtain ⟨⟨h₃, -⟩, -⟩ := Fval' hβ' ex,
    rw hspec hβ, exact h₃,
  have h₄ : ∀ {β : Set}, β ∈ h.dom → β ⊆ h.dom,
    intros β hβ δ δβ, rw h₂ at hβ ⊢, rcases hβ with ⟨βf, γ, γf, hγ⟩,
    refine ⟨ord_mem_trans fdom δβ βf, γ, γf, _⟩,
    intros α αδ, exact hγ (ord_mem_trans (ord_of_mem_ord fdom βf) αδ δβ),
  have h₅ : ∀ {β : Set}, β ∈ h.dom → h.fun_value β = F' (h.restrict β),
    intros β hβ, have βord := ord_of_mem_ord fdom (hdom hβ), revert β βord, refine trans_ind_schema _,
    intros β βord ind hβ,
    have h₅ : h.restrict β = F.restrict β, apply fun_ext (restrict_is_function hfun) (restrict_is_function Ffun),
        rw restrict_dom (h₄ hβ), symmetry, apply restrict_dom, rw Fdom, refine subset_trans _ hdom,
        exact h₄ hβ,
      intros δ δβ, rw restrict_dom (h₄ hβ) at δβ, rw [restrict_fun_value hfun (h₄ hβ) δβ, hspec (h₄ hβ δβ)],
      symmetry, refine restrict_fun_value Ffun _ δβ,
      rw Fdom, exact subset_trans (h₄ hβ) hdom,
    rw [hspec hβ, Fspec (hdom hβ), h₅],
  have h₆ : ∀ {β : Set}, β ∈ h.dom → ∃ γ : Set, R β γ,
    intros β hβ,
    have hf := h₂.mp hβ, obtain ⟨βf, γ, γf, hγ⟩ := hf,
    refine ⟨_, γf, λ δ δβ, _⟩, rw hspec (h₄ hβ δβ), exact hγ δβ,
  have h₇ : ∀ {β : Set}, β ∈ h.dom → ∀ {γ : Set}, Q β γ ↔ R β γ,
    intros β hβ γ, dsimp [Q, R], rw and.congr_right_iff, intro γf, apply forall_congr, intro δ,
    apply imp_congr_right, intro δβ, rw hspec (h₄ hβ δβ),
  have h₈ : ∀ {β : Set}, β ∈ h.dom → R β (h.fun_value β) ∧ ∀ {α : Set}, R β α → h.fun_value β ≤ α,
    intros β hβ, simp only [←h₇ hβ, hspec hβ],
    obtain ⟨βf, hβ'⟩ := h₂.mp hβ,
    exact Fval' βf hβ',
  have hord : h.dom.is_ordinal := ord_of_sub_ord fdom hdom (transitive_set_iff'.mpr @h₄),
  let g : Set := f.comp h,
  have gfun := T3H_a ffun hfun,
  have h₉ : h.ran ⊆ f.dom, intro y, rw mem_ran_iff hfun, rintro ⟨β, hβ, he⟩, subst he, exact h₃ hβ,
  have gdom := dom_comp h₉,
  have gdom' : g.dom ≤ f.dom, rw [gdom, ord_le_iff_sub hord fdom], exact hdom,
  have gords : ∀ {δ : Set}, δ ∈ g.ran → δ.is_ordinal := λ δ hδ, ford (ran_comp_sub hδ),
  have gord : g.dom.is_ordinal, rw gdom, exact hord,
  have gval : ∀ {β : Set}, β ∈ g.dom → g.fun_value β = f.fun_value (h.fun_value β),
    intros β hβ, rw T3H_c ffun hfun hβ,
  refine ⟨_, gfun, gord, gdom', @gords, λ η hη, _, _⟩,
    rw gdom at hη, have h := (h₈ hη).left.right,
    rw ←gdom at hη, intros ξ ξη,
    rw [gval hη, gval (ord_mem_trans gord ξη hη)], exact h ξη,
  rw eq_iff_subset_and_subset, refine ⟨ran_comp_sub, _, Union_sub_of_sub ran_comp_sub⟩,
  suffices h₁₀ : ∀ {β : Set}, β ∈ f.dom → ∃ α : Set, α ∈ g.dom ∧ f.fun_value β ≤ g.fun_value α,
    intro δ, simp only [mem_Union, exists_prop, mem_ran_iff ffun],
    rintro ⟨β, ⟨β, hβ, he⟩, δβ⟩, subst he,
    obtain ⟨α, hα, βα⟩ := h₁₀ hβ,
    exact ⟨_, fun_value_def'' gfun hα, ord_lt_of_lt_of_le (gords (fun_value_def'' gfun hα)) δβ βα⟩,
  have h₁₁ : ∀ {ξ : Set}, ξ ∈ h.dom → ∀ {δ : Set}, δ ∈ f.dom → δ ≤ h.fun_value ξ → f.fun_value δ ≤ g.fun_value ξ,
    intros ξ ξh δ δf δξ, rw ←gdom at ξh,
    rw [←ord_not_lt_iff_le (gords (fun_value_def'' gfun ξh)) (ford (fun_value_def'' ffun δf)), gval ξh],
    intro h', suffices δξ' : δ = h.fun_value ξ,
      subst δξ', exact not_mem_self h',
    rw gdom at ξh,
    rw ord_eq_iff_le_and_le (ord_of_mem_ord fdom δf) (ord_of_mem_ord fdom (h₉ (fun_value_def'' hfun ξh))),
    refine ⟨δξ, _⟩, apply (h₈ ξh).right ⟨δf, λ α αξ, _⟩,
    exact ord_mem_trans (ford (fun_value_def'' ffun δf)) ((h₈ ξh).left.right αξ) h',

  have hmon : ∀ {α : Set}, α ∈ h.dom → ∀ {β : Set}, β ∈ α → h.fun_value β ∈ h.fun_value α,
    intros α αh β βα,
    have hαord : (h.fun_value α).is_ordinal := ord_of_mem_ord fdom (h₉ (fun_value_def'' hfun αh)),
    have hβord : (h.fun_value β).is_ordinal := ord_of_mem_ord fdom (h₉ (fun_value_def'' hfun (ord_mem_trans hord βα αh))),
    rw ←ord_not_le_iff_lt hαord hβord, intro αβ, cases αβ,
      refine not_mem_self (ord_lt_of_lt_of_le hαord αβ ((h₈ (ord_mem_trans hord βα αh)).right _)),
      dsimp [R], refine ⟨h₉ (fun_value_def'' hfun αh), λ δ δβ, ord_mem_trans (ford (fun_value_def'' ffun _)) ((h₈ (ord_mem_trans hord βα αh)).left.right δβ) _⟩,
        exact h₉ (fun_value_def'' hfun αh),
      exact (h₈ αh).left.right βα,
    have h' := (h₈ αh).left.right βα,
    rw αβ at h', exact not_mem_self h',
  have h₁₂ : ∀ {ξ : Set}, ξ ∈ h.dom → ξ ≤ h.fun_value ξ,
    intros ξ ξh, have ξord : ξ.is_ordinal := ord_of_mem_ord hord ξh, revert ξ ξord, refine trans_ind_schema _,
    intros ξ ξord ind ξh,
    rw ord_le_iff_sub ξord (ord_of_mem_ord fdom (h₉ (fun_value_def'' hfun ξh))),
    intros β βξ, exact ord_lt_of_le_of_lt (ord_of_mem_ord fdom (h₉ (fun_value_def'' hfun ξh))) (ind βξ (ord_mem_trans hord βξ ξh)) (hmon ξh βξ),
  have h₁₃ : ∀ {ξ : Set}, ξ ∈ g.dom → f.fun_value ξ ≤ g.fun_value ξ,
    intros ξ ξg, rw gdom at ξg, exact h₁₁ ξg (hdom ξg) (h₁₂ ξg),
  have h₁₄ : ∀ {β : Set}, β ∈ f.dom → ∀ {γ : Set}, R β γ → Q β γ,
    rintros β βf γ ⟨γf, h'⟩, refine ⟨γf, λ δ δβ, _⟩,
    by_cases h'' : δ ∈ h.dom,
      rw ←hspec h'', exact h' δβ,
    rw h₂ at h'',
    replace h'' : ¬ ∃ γ : Set, Q δ γ, intro h''', exact h'' ⟨ord_mem_trans fdom δβ βf, h'''⟩,
    rw Fval (ord_mem_trans fdom δβ βf) h'',
    have a_very_interesting_lemma : ∀ {f x : Set}, x ∉ f.dom → f.fun_value x = ∅,
      intros f x xf, rw eq_empty, dsimp [fun_value], intros z hz,
      rw mem_Union at hz, simp only [exists_prop, mem_sep] at hz,
      rcases hz with ⟨y, ⟨yf, xy⟩, zy⟩, apply xf, rw mem_dom, exact ⟨_, xy⟩,
    rw a_very_interesting_lemma not_mem_self,
    exact ord_pos_of_inhab (ford (fun_value_def'' ffun γf)) ⟨_, h' δβ⟩,
  cases gdom',
    suffices h' : ¬ ∃ γ : Set, γ ∈ f.dom ∧ R (g.dom) γ,
      dsimp [R] at h', push_neg at h', intros β βf,
      obtain ⟨δ, δg, h''⟩ := h' _ βf βf, refine ⟨_, δg, _⟩,
      rw ←ord_not_lt_iff_le (gords (fun_value_def'' gfun δg)) (ford (fun_value_def'' ffun βf)),
      rw gval δg, exact h'',
    rintros ⟨γ, γf, hR⟩,
    apply @not_mem_self g.dom, rw [gdom, h₂], rw ←gdom, exact ⟨gdom', _, h₁₄ gdom' hR⟩,
  intros β βf, rw ←gdom' at βf, exact ⟨_, βf, h₁₃ βf⟩,
end

lemma card_ord_le_self {β : Set} (βord : β.is_ordinal) : β.card ≤ β :=
card_least βord equin_refl

lemma cf_limit_inf {γ : Set} (γord : γ.limit_ord) : ¬ γ.cf.finite_cardinal :=
begin
  obtain ⟨S, ⟨Sγ, γS⟩, cardS⟩ := cf_limit γord,
  rw [←cardS, card_finite_iff_finite], apply unbounded_ords_inf γord.ord Sγ,
    apply inhabited_of_ne_empty, intro Se, subst Se, rw Union_empty at γS,
    exact ne_empty_of_inhabited _ (limit_ord_inhab γord) γS,
  refine classical.by_contradiction _, intro h, push_neg at h,
  replace h : ∃ n : Set, n ∈ S ∧ ∀ {m : Set}, m ∈ S → m ≤ n,
    rcases h with ⟨n, nS, h⟩, refine ⟨_, nS, λ m mS, _⟩,
    rw ←ord_not_lt_iff_le (ord_of_mem_ord γord.ord (Sγ nS)) (ord_of_mem_ord γord.ord (Sγ mS)),
    exact h _ mS,
  apply @not_mem_self γ, nth_rewrite 0 γS, apply Sγ,
  exact (case_exists_bound (λ x xS, ord_of_mem_ord γord.ord (Sγ xS)) h).left,
end

lemma cf_le_self {γ : Set} (γord : γ.is_ordinal) : γ.cf ≤ γ :=
ord_le_trans γord (cf_ord_le_card γord) (card_ord_le_self γord)

theorem T9Q {γ : Set} (γord : γ.limit_ord) :
  ∃ f : Set, f.into_fun γ.cf γ
  ∧ (∀ {η : Set}, η ∈ f.dom → ∀ {ξ : Set}, ξ ∈ η → f.fun_value ξ ∈ f.fun_value η)
  ∧ f.ran.Union = γ :=
begin
  have h : ∃ f : Set, f.into_fun γ.cf γ ∧ γ = f.ran.Union,
    obtain ⟨S, ⟨Sγ, γS⟩, cardS⟩ := cf_limit γord,
    rw [←card_of_cardinal_eq_self (cf_is_card γord.ord), card_equiv] at cardS,
    replace cardS := equin_symm cardS, obtain ⟨F, Fonto, Foto⟩ := cardS,
    refine ⟨_, comp_into_fun (into_of_onto Fonto) (into_of_into_ran_sub Sγ id_into), _⟩,
    suffices h : (S.id.comp F).ran = S, rwa h,
    nth_rewrite 1 ←(@id_onto S).right.right, apply ran_comp,
    rw [id_onto.right.left, Fonto.right.right], exact subset_self,
  obtain ⟨f, finto, fran⟩ := h,
  have fdom : f.dom.is_ordinal, rw finto.right.left, exact card_is_ord (cf_is_card γord.ord),
  have ford : ∀ ⦃δ : Set⦄, δ ∈ f.ran → δ.is_ordinal, intros δ δf,
    exact ord_of_mem_ord γord.ord (finto.right.right δf),
  obtain ⟨g, gfun, gord, gdom, gords, inc, gran, h⟩ := exists_sub_ord_seq finto.left fdom ford,
  rw ←fran at h,
  have gran' : g.ran ⊆ γ := subset_trans gran finto.right.right,
  have gdom' : g.dom = γ.cf, rw finto.right.left at gdom,
    rw ord_eq_iff_le_and_le gord (card_is_ord (cf_is_card γord.ord)),
    refine ⟨gdom, ord_le_trans gord (cf_limit_least γord ⟨gran', h⟩) _⟩,
    have h' : g.ran.card = g.dom.card, rw card_equiv, apply equin_symm, refine ⟨_, ⟨gfun, rfl, rfl⟩, one_to_one_of gfun (λ m hm n hn mn gmn, _)⟩,
      cases ord_conn (ord_of_mem_ord gord hm) (ord_of_mem_ord gord hn) mn with mln nlm,
        specialize inc hn mln, rw gmn at inc, exact not_mem_self inc,
      specialize inc hm nlm, rw gmn at inc, exact not_mem_self inc,
    rw h', exact card_ord_le_self gord,
  exact ⟨_, ⟨gfun, gdom', gran'⟩, @inc, h.symm⟩,
end

theorem C9R {γ : Set} (γord : γ.limit_ord) {α : Set} (αord : α.is_ordinal)
  {f : Set} (finto : f.into_fun α γ)
  (inc : ∀ {η : Set}, η ∈ f.dom → ∀ {ξ : Set}, ξ ∈ η → f.fun_value ξ ∈ f.fun_value η)
  (conv : f.ran.Union = γ) : γ.cf ≤ α :=
begin
  apply ord_le_trans αord (cf_limit_least γord ⟨finto.right.right, conv.symm⟩),
  have ford : f.dom.is_ordinal, rwa finto.right.left,
  have h : f.ran.card = f.dom.card, rw card_equiv, apply equin_symm, refine ⟨_, ⟨finto.left, rfl, rfl⟩, one_to_one_of finto.left (λ m hm n hn mn gmn, _)⟩,
    cases ord_conn (ord_of_mem_ord ford hm) (ord_of_mem_ord ford hn) mn with mln nlm,
      specialize inc hn mln, rw gmn at inc, exact not_mem_self inc,
    specialize inc hm nlm, rw gmn at inc, exact not_mem_self inc,
  rw [h, finto.right.left], exact card_ord_le_self αord,
end

-- Theorem 9S
theorem cf_ord_regular {γ : Set} (γord : γ.is_ordinal) : γ.cf.regular :=
begin
  rcases ord_cases γord with (γz|(⟨β, γβ⟩|γord')),
  { subst γz, rw cf_zero, exact cf_zero, },
  { subst γβ, rw cf_succ, exact cf_succ, },
  { rw regular_iff_ne (cf_is_card γord) (cf_limit_inf γord'),
    rintros S ⟨γS, Sγ⟩,
    suffices h : γ.cf.card_le S.card,
      refine card_eq_of_le_of_le card_is_card (cf_is_card γord) _ h,
      rw ←card_of_cardinal_eq_self (cf_is_card γord), exact card_le_of_subset γS,
    obtain ⟨f, finto, inc, fran⟩ := T9Q γord',
    have ford : f.dom.is_ordinal, rw finto.right.left, exact card_is_ord (cf_is_card γord),
    let g := f.restrict S,
    have hS : S ⊆ f.dom, rwa finto.right.left,
    have gonto : g.onto_fun S (f.img S) := ⟨restrict_is_function finto.left, restrict_dom hS, restrict_ran⟩,
    have gval : ∀ {β : Set}, β ∈ g.dom → g.fun_value β = f.fun_value β,
      intros β hβ, have hβ' : β ∈ S, rwa ←gonto.right.left, exact restrict_fun_value finto.left hS hβ',
    have gdom : g.dom ⊆ f.dom, rw gonto.right.left, exact hS,
    have h : S.card = (f.img S).card, rw card_equiv, refine ⟨_, gonto, one_to_one_of (restrict_is_function finto.left) (λ m hm n hn mn gmn, _)⟩,
      rw [gval hm, gval hn] at gmn,
      cases ord_conn (ord_of_mem_ord ford (gdom hm)) (ord_of_mem_ord ford (gdom hn)) mn with mln nlm,
        specialize inc (gdom hn) mln, rw gmn at inc, exact not_mem_self inc,
      specialize inc (gdom hm) nlm, rw gmn at inc, exact not_mem_self inc,
    rw [h, card_le_iff_le (cf_is_card γord) card_is_card],
    refine cf_limit_least γord' ⟨subset_trans img_subset_ran finto.right.right, _⟩,
    rw eq_iff_subset_and_subset, split,
    { intros α αγ, simp only [←fran, mem_Union, exists_prop, mem_ran_iff finto.left] at αγ,
      rcases αγ with ⟨fβ, ⟨β, βf, fβfβ⟩, αfβ⟩, subst fβfβ,
      rw [finto.right.left, Sγ, mem_Union] at βf, rcases βf with ⟨δ, δS, βδ⟩,
      rw mem_Union, refine ⟨_, fun_value_mem_img finto.left hS δS, ord_mem_trans _ αfβ (inc (hS δS) βδ)⟩,
      exact ord_of_mem_ord γord (finto.right.right (fun_value_def'' finto.left (hS δS))), },
    { exact Union_sub (λ y hy β βy, ord_mem_trans γord βy (subset_trans img_subset_ran finto.right.right hy)), }, },
end

-- Theorem 9T
theorem cf_inf_card {γ : Set} (γcard : γ.is_cardinal) (γinf : ¬ γ.finite_cardinal) :
  ∃ S : Set, (∀ {x : Set}, x ∈ S → x.card.card_lt γ) ∧ γ = S.Union ∧ S.card = γ.cf :=
begin
  obtain ⟨S, ⟨Sγ, γS⟩, cardS⟩ := cf_limit (inf_card_is_limit γcard γinf),
  refine ⟨_, λ α αS, card_lt_of_mem card_is_card γcard (ord_lt_of_le_of_lt (card_is_ord γcard) _ (Sγ αS)), γS, cardS⟩,
  exact card_ord_le_self (ord_of_mem_ord (card_is_ord γcard) (Sγ αS)),
end

theorem cf_inf_card_least {γ : Set} (γcard : γ.is_cardinal) (γinf : ¬ γ.finite_cardinal)
  {S : Set} (hS : ∀ {x : Set}, x ∈ S → x.card.card_lt γ) (un : γ = S.Union) : γ.cf.card_le S.card :=
begin
  let μ := (repl_img card S).Union,
  have hμ : μ.is_cardinal, apply Union_card_is_card,
    apply of_repl_img, intros α αS, exact card_is_card,
  have h : ∀ ⦃α : Set⦄, α ∈ S → α.card.card_le μ,
    intros α αS, rw [←card_of_cardinal_eq_self hμ, ←@card_of_cardinal_eq_self α.card card_is_card],
    apply card_le_of_subset, intros β βα, simp only [mem_Union, exists_prop, mem_repl_img],
    exact ⟨_, ⟨_, αS, rfl⟩, βα⟩,
  have hγ : γ.card_le (S.card.card_mul μ),
    rw [←card_of_cardinal_eq_self γcard, un], exact ch6_26 hμ h,
  by_cases hc : γ.card_le S.card,
    refine card_le_trans γcard _ hc,
    rw card_le_iff_le (cf_is_card (card_is_ord γcard)) γcard, exact cf_card γcard,
  rw card_not_le_iff_lt γcard card_is_card at hc,
  have γμ : γ = μ,
  { have μγ : μ.card_le γ, rw [←card_of_cardinal_eq_self hμ, ←card_of_cardinal_eq_self γcard],
      apply card_le_of_subset, intros α, simp only [mem_Union, exists_prop, mem_repl_img],
      rintro ⟨z, ⟨x, xS, zx⟩, αx⟩, subst zx, apply ord_mem_trans (card_is_ord γcard) αx,
      rw ←card_lt_iff_mem card_is_card γcard, exact hS xS,
    rw card_le_iff at μγ, cases μγ, rotate,
      exact μγ.symm,
    exfalso, suffices h : γ.card_lt γ, from h.right rfl,
    nth_rewrite 1 ←mul_infinite_card_eq_self γcard γinf,
    apply card_lt_of_le_of_lt γcard (mul_cardinal (@card_is_card S) hμ) hγ,
    exact card_mul_lt_of_lt_of_lt γcard card_is_card hc hμ μγ, },
  refine card_le_trans (@card_is_card (repl_img card S)) _ repl_img_card_le,
  rw card_le_iff_le (cf_is_card (card_is_ord γcard)) card_is_card,
  apply cf_limit_least (inf_card_is_limit γcard γinf) ⟨_, γμ⟩,
  intro z, rw mem_repl_img, rintro ⟨x, xS, zx⟩, subst zx,
  rw ←card_lt_iff_mem card_is_card γcard, exact hS xS,
end

-- skipped Konig's theorem and the rest because I'm now completely lost

end Set