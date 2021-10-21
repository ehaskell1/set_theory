import ch7_cont
universe u
namespace Set

local attribute [irreducible] mem

noncomputable def con_fun (G : Set → Set) (α : Set) : Set := trans_rec α α.eps_order G
lemma con_fun_fun {G : Set → Set} {α : Set} (αord : α.is_ordinal) : (con_fun G α).is_function := trans_rec_fun (ordinal_well_ordered αord)
lemma con_fun_dom {G : Set → Set} {α : Set} (αord : α.is_ordinal) : (con_fun G α).dom = α := trans_rec_dom (ordinal_well_ordered αord)

noncomputable def ord_rec (G : Set → Set) : Set → Set :=
fun α, (con_fun G α.succ).fun_value α

lemma con_unique {G : Set → Set}
{f : Set} (ffun : f.is_function) (fdom : f.dom.is_ordinal) (fspec : ∀ {β : Set}, β ∈ f.dom → f.fun_value β = G (f.restrict β))
{g : Set} (gfun : g.is_function) (gdom : g.dom.is_ordinal) (gspec : ∀ {β : Set}, β ∈ g.dom → g.fun_value β = G (g.restrict β))
{α : Set} (αfg : α ∈ f.dom ∩ g.dom) : f.fun_value α = g.fun_value α :=
begin
  have αord : α.is_ordinal, apply ord_of_mem_ord fdom, rw mem_inter at αfg, exact αfg.left,
  revert α αord, refine trans_ind_schema _, intros α αord ind αfg,
  rw mem_inter at αfg, rw [fspec αfg.left, gspec αfg.right], congr' 1,
  have αf : α ⊆ f.dom, rw ←ord_le_iff_sub αord fdom, left, exact αfg.left,
  have αg : α ⊆ g.dom, rw ←ord_le_iff_sub αord gdom, left, exact αfg.right,
  apply fun_ext (restrict_is_function ffun) (restrict_is_function gfun),
    rw [restrict_dom αf, restrict_dom αg],
  intros β βα, rw restrict_dom αf at βα,
  rw [restrict_fun_value ffun αf βα, restrict_fun_value gfun αg βα],
  apply ind βα, rw mem_inter, cases αfg, split; refine ord_mem_trans _ βα _; assumption,
end

lemma con_fun_spec {G : Set → Set} {α : Set} (αord : α.is_ordinal) ⦃β : Set⦄ (βα : β ∈ α) : (con_fun G α).fun_value β = ord_rec G β :=
begin
  have βord' := succ_ord_of_ord (ord_of_mem_ord αord βα),
  refine @con_unique G _ (con_fun_fun αord) _ _ _ (con_fun_fun βord') _ _ _ _,
  { rw con_fun_dom αord, exact αord, },
  { intros β βα, rw con_fun_dom αord at βα,
    rw [con_fun, trans_rec_spec (ordinal_well_ordered αord) βα, seg_ord_eq_self αord βα], },
  { rw con_fun_dom βord', exact βord', },
  { intros β ββ, rw con_fun_dom βord' at ββ,
    rw [con_fun, trans_rec_spec (ordinal_well_ordered βord') ββ, seg_ord_eq_self βord' ββ], },
  { rw [con_fun_dom αord, con_fun_dom βord', mem_inter],
    exact ⟨βα, self_mem_succ⟩, },
end

lemma ord_rec_spec {G : Set → Set} {α : Set} (αord : α.is_ordinal) : ord_rec G α = G (con_fun G α) :=
begin
  have αord' := succ_ord_of_ord αord,
  rw [ord_rec], dsimp, rw [con_fun, trans_rec_spec (ordinal_well_ordered αord') self_mem_succ],
  congr, apply fun_ext (restrict_is_function (trans_rec_fun (ordinal_well_ordered αord'))) (con_fun_fun αord),
    rw [con_fun_dom αord, seg_ord_eq_self αord' self_mem_succ],
    apply restrict_dom, rw trans_rec_dom (ordinal_well_ordered αord'), exact self_sub_succ,
  intros β βα, rw seg_ord_eq_self αord' self_mem_succ at *,
  rw [restrict_dom_inter, trans_rec_dom (ordinal_well_ordered αord'), inter_comm, inter_eq_of_sub self_sub_succ] at βα,
  rw restrict_fun_value (trans_rec_fun (ordinal_well_ordered αord')) _ βα, swap,
    rw trans_rec_dom (ordinal_well_ordered αord'), exact self_sub_succ,
  rw [←con_fun, con_fun_spec αord' (self_sub_succ βα), con_fun_spec αord βα],
end

lemma con_fun_ran_eq {f : Set → Set} {α : Set} (αord : α.is_ordinal) : (con_fun f α).ran = repl_img (ord_rec f) α :=
begin
  rw eq_iff_subset_and_subset, split,
    rw subset_def, apply @of_ran _ (@con_fun_fun f _ αord) (λ y, y ∈ repl_img (ord_rec f) α),
    intros β βα, rw con_fun_dom αord at βα, rw [con_fun_spec αord βα, mem_repl_img], finish,
  apply of_repl_img, intros β βα, rw mem_ran_iff (con_fun_fun αord),
  rw [con_fun_dom αord, ←con_fun_spec αord βα], finish,
end

theorem Veb_eq' {α : Set} (αord : α.is_ordinal) : α.Veb = ord_rec (fun f, f.ran.powersets.Union) α :=
begin
  revert α, apply trans_ind_schema, intros α αord ind,
  rw [ord_rec_spec αord, Veb_eq αord], congr, apply ext,
  intro X, rw [mem_Veb_img, mem_ran_iff (con_fun_fun αord), con_fun_dom αord],
  apply exists_congr, intro β, rw and.congr_right_iff, intro βα,
  rw [ind βα, ord_rec], dsimp, apply eq_iff_eq_cancel_left.mpr,
  rw [con_fun_spec αord βα, con_fun_spec (succ_ord_of_ord (ord_of_mem_ord αord βα)) self_mem_succ],
end

lemma exists_not_mem {p : Set → Prop} (pclass : ¬ ∃ X : Set, ∀ {z : Set}, z ∈ X ↔ p z)
{X : Set} : ∃ x : Set, p x ∧ x ∉ X :=
begin
  apply classical.by_contradiction, intro h, push_neg at h,
  apply pclass, use {z ∈ X | p z}, intro z,
  rw [mem_sep, and_iff_right_iff_imp], exact h _,
end

lemma ord_set_exists_iff_bounded {p : Set → Prop} (pord : ∀ {α : Set}, p α → α.is_ordinal) :
  (∃ X : Set, ∀ {α : Set}, α ∈ X ↔ p α) ↔ ∃ β : Set, β.is_ordinal ∧ ∀ {α : Set}, p α → α ≤ β :=
begin
  split,
    refine classical.by_contradiction _, intro h,
    push_neg at h, rcases h with ⟨⟨X, hX⟩, h⟩,
    refine not_exists_ord_set ⟨X.Union, _⟩, intro β, simp only [mem_Union, exists_prop], split,
      rintro ⟨γ, γX, βγ⟩, refine ord_of_mem_ord _ βγ,
      apply pord, rw ←hX, exact γX,
    intro βord, rcases h _ βord with ⟨α, pα, βα⟩,
    rw ord_not_le_iff_lt (pord pα) βord at βα,
    use α, rw hX, exact ⟨pα, βα⟩,
  rintro ⟨β, -, h⟩, use {α ∈ β.succ | p α},
  intro α, rw [mem_sep, and_iff_right_iff_imp],
  rw mem_succ_iff_le, exact h,
end

local attribute [instance] classical.prop_decidable

lemma exists_least_inf_card (X : Set) : ∃ κ : Set, κ.is_cardinal ∧ ¬ κ.finite_cardinal ∧ κ ∉ X
  ∧ ∀ {μ : Set}, μ.is_cardinal → ¬ μ.finite_cardinal → μ ∉ X → κ.card_le μ :=
begin
  have h₁ : ∃ κ : Set, (κ.is_cardinal ∧ ¬ κ.finite_cardinal) ∧ κ ∉ X,
    apply exists_not_mem, rw ord_set_exists_iff_bounded, swap,
      rintros α ⟨αcard, -⟩, exact card_is_ord αcard,
    push_neg, intros α αord,
    by_cases αfin : α.is_finite,
      refine ⟨card ω, ⟨⟨_, rfl⟩, aleph_null_infinite_cardinal⟩, _⟩,
      rw [ord_not_le_iff_lt (card_is_ord ⟨_, rfl⟩) αord, card_of_cardinal_eq_self omega_is_card],
      apply ord_lt_of_card_lt αord omega_is_ord,
      exact finite_card_lt_aleph_null' αfin,
    have exp_card := exp_cardinal (nat_is_cardinal two_nat) ⟨α, rfl⟩,
    have lt : α.card.card_lt (card_exp two α.card) := card_lt_exp ⟨_, rfl⟩,
    refine ⟨card_exp two α.card, ⟨exp_card, _⟩, _⟩,
    refine card_inf_of_ge_inf ⟨α, rfl⟩ _ exp_card _,
        rw card_finite_iff_finite, exact αfin,
      rw card_le_iff, left, exact lt,
    rw [ord_not_le_iff_lt (card_is_ord exp_card) αord],
    apply ord_lt_of_card_lt αord (card_is_ord exp_card),
    rw card_of_cardinal_eq_self exp_card, exact lt,
  have h₂ : ∃ κ : Set, κ.is_ordinal ∧ κ.is_cardinal ∧ ¬ κ.finite_cardinal ∧ κ ∉ X,
    rcases h₁ with ⟨κ, ⟨κcard, κfin⟩, κX⟩, exact ⟨_, card_is_ord κcard, κcard, κfin, κX⟩,
  obtain ⟨κ, κord, ⟨κcard, κfin, κX⟩, least⟩ := exists_least_ord_of_exists h₂,
  refine ⟨_, κcard, κfin, κX, λ μ μcard μfin μX, _⟩,
  specialize least (card_is_ord μcard) ⟨μcard, μfin, μX⟩,
  rw card_le_iff_le κcard μcard, exact least,
end

noncomputable def Aleph : Set → Set := ord_rec (fun f, classical.some (exists_least_inf_card f.ran))
lemma Aleph_spec {α : Set} (αord : α.is_ordinal) : α.Aleph.is_cardinal ∧ ¬ α.Aleph.finite_cardinal ∧ α.Aleph ∉ (con_fun (fun f, classical.some (exists_least_inf_card f.ran)) α).ran
  ∧ ∀ {μ : Set}, μ.is_cardinal → ¬ μ.finite_cardinal → μ ∉ (con_fun (fun f, classical.some (exists_least_inf_card f.ran)) α).ran → α.Aleph.card_le μ :=
begin
  rw [Aleph, ord_rec_spec αord], exact classical.some_spec (exists_least_inf_card _),
end

lemma Aleph_is_card {α : Set} (αord : α.is_ordinal) : α.Aleph.is_cardinal :=
begin
  obtain ⟨αcard, -, -, -⟩ := Aleph_spec αord,
  exact αcard,
end
lemma Aleph_inf {α : Set} (αord : α.is_ordinal) : ¬ α.Aleph.finite_cardinal :=
begin
  obtain ⟨-, αfin, -, -⟩ := Aleph_spec αord,
  exact αfin,
end
lemma Aleph_not_eq_of_mem {α : Set} (αord : α.is_ordinal) {β : Set} (βα : β ∈ α) : α.Aleph ≠ β.Aleph :=
begin
  obtain ⟨-, -, αne, -⟩ := Aleph_spec αord,
  intro αβ, apply αne, rw [mem_ran_iff (con_fun_fun αord), con_fun_dom αord],
  refine ⟨_, βα, _⟩, rw con_fun_spec αord βα, exact αβ,
end
lemma Aleph_least {α : Set} (αord : α.is_ordinal)
  {κ : Set} (κcard : κ.is_cardinal) (κfin : ¬ κ.finite_cardinal) (κne : ∀ {β : Set}, β ∈ α → κ ≠ β.Aleph) :
  α.Aleph.card_le κ :=
begin
  obtain ⟨-, -, -, least⟩ := Aleph_spec αord,
  apply least κcard κfin, intro κα,
  rw [mem_ran_iff (con_fun_fun αord), con_fun_dom αord] at κα,
  rcases κα with ⟨β, βα, κβ⟩, subst κβ, apply κne βα,
  rw [con_fun_spec αord βα, Aleph],
end

-- Theorem 8A(a)
theorem Aleph_lt_of_mem {β : Set} (βord : β.is_ordinal) {α : Set} (αβ : α ∈ β) : α.Aleph.card_lt β.Aleph :=
begin
  have αord := ord_of_mem_ord βord αβ,
  split,
    apply Aleph_least αord (Aleph_is_card βord) (Aleph_inf βord),
    intros γ γα, exact Aleph_not_eq_of_mem βord (ord_mem_trans βord γα αβ),
  symmetry, exact Aleph_not_eq_of_mem βord αβ,
end

lemma ord_le_Aleph_self {α : Set.{u}} (αord : α.is_ordinal) : α ≤ α.Aleph :=
begin
  rw ←ord_not_lt_iff_le (card_is_ord (Aleph_is_card αord)) αord,
  let f : Set := rec_fun' (λ κ, κ.Aleph) α,
  have ford : ∀ {n : Set.{u}}, n ∈ nat.{u} → (f.fun_value n).is_ordinal, apply induction,
      rw rec_fun_base', exact αord,
    intros n nω ind, rw rec_fun_ind' nω, exact card_is_ord (Aleph_is_card ind),
  intro αα, refine no_ω_cycle ⟨f, rec_fun_fun', rec_fun_dom', _⟩,
  apply induction,
    rw [rec_fun_ind' zero_nat, rec_fun_base'], exact αα,
  intros n nω ind,
  have nω' := nat_induct.succ_closed nω,
  rw [rec_fun_ind' nω, rec_fun_ind' nω', ←card_lt_iff_mem (Aleph_is_card (ford nω')) (Aleph_is_card (ford nω))],
  exact Aleph_lt_of_mem (ford nω) ind,
end

-- Theorem 8A(b)
theorem inf_card_eq_Aleph {κ : Set.{u}} (κcard : κ.is_cardinal) (κinf : ¬ κ.finite_cardinal) : ∃ α : Set, α.is_ordinal ∧ κ = α.Aleph :=
begin
  have κord : κ.is_ordinal := card_is_ord κcard,
  revert κ κord, refine trans_ind_schema _, intros κ κord κind κcard κinf,
  let X : Set := {β ∈ κ | β.is_ordinal ∧ β.Aleph.card_lt κ},
  have memX : ∀ {β : Set}, β ∈ X ↔ β.is_ordinal ∧ β.Aleph.card_lt κ,
    simp only [mem_sep, and_iff_right_iff_imp],
    rintros β ⟨βord, βκ⟩, apply ord_lt_of_le_of_lt κord (ord_le_Aleph_self βord),
    rw ←card_lt_iff_mem (Aleph_is_card βord) κcard, exact βκ,
  have Xord : X.is_ordinal, apply trans_ords_is_ord,
      intros α αX, rw memX at αX, exact αX.left,
    rw transitive_set_iff, intros α αX β βα, rw memX at αX ⊢,
    have βord := ord_of_mem_ord αX.left βα,
    refine ⟨βord, _⟩,
    refine card_lt_trans (Aleph_is_card βord) (Aleph_is_card αX.left) _ αX.right,
    exact Aleph_lt_of_mem αX.left βα,
  have XAord : X.Aleph.is_ordinal := card_is_ord (Aleph_is_card Xord),
  refine ⟨_, Xord, _⟩, rw ord_eq_iff_le_and_le κord XAord, split,
    rw ←ord_not_lt_iff_le XAord κord, intro Xκ,
    rw ←card_lt_iff_mem (Aleph_is_card Xord) κcard at Xκ,
    apply ord_mem_irrefl Xord, rw memX, exact ⟨Xord, Xκ⟩,
  rw ←card_le_iff_le (Aleph_is_card Xord) κcard,
  apply Aleph_least Xord κcard κinf,
  intros β βX, rw memX at βX, symmetry, exact βX.right.right,
end

lemma Aleph_oto' {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal)
  (αβ : α.Aleph.card_lt β.Aleph) : α ∈ β :=
begin
  rw ←ord_not_le_iff_lt βord αord, rintro (βα|βα),
    exact not_card_lt_cycle (Aleph_is_card αord) (Aleph_is_card βord) ⟨αβ, Aleph_lt_of_mem αord βα⟩,
  subst βα, exact αβ.right rfl,
end

lemma Aleph_imm {α : Set} (αord : α.is_ordinal) : ¬ ∃ κ : Set, κ.is_cardinal ∧ α.Aleph.card_lt κ ∧ κ.card_lt α.succ.Aleph :=
begin
  rintro ⟨κ, κcard, ακ, κα⟩,
  have κinf : ¬ κ.finite_cardinal, apply card_inf_of_ge_inf (Aleph_is_card αord) (Aleph_inf αord) κcard,
    rw card_le_iff, left, exact ακ,
  obtain ⟨β, βord, κβ⟩ := inf_card_eq_Aleph κcard κinf, subst κβ,
  apply succ_imm α ⟨_, Aleph_oto' αord βord ακ, Aleph_oto' βord (succ_ord_of_ord αord) κα⟩,
end

lemma Aleph_le_of_lt_succ {α : Set} (αord : α.is_ordinal) {κ : Set} (κcard : κ.is_cardinal)
  (κα : κ.card_lt α.succ.Aleph) : κ.card_le α.Aleph :=
begin
  rw ←card_not_lt_iff_le (Aleph_is_card αord) κcard, intro ακ,
  exact Aleph_imm αord ⟨_, κcard, ακ, κα⟩,
end

lemma Aleph_zero_eq : Aleph ∅ = card ω :=
begin
  have zord := nat_is_ord zero_nat,
  have zcard := (Aleph_is_card zord),
  apply card_eq_of_le_of_le zcard ⟨_, rfl⟩,
    apply Aleph_least zord ⟨_, rfl⟩ aleph_null_infinite_cardinal,
    simp only [mem_empty, forall_false_left, forall_const],
  apply aleph_null_least_infinite_cardinal zcard,
  exact Aleph_inf zord,
end

-- Lemma 8B
lemma Union_card_is_card {X : Set} (Xcard : ∀ {κ : Set}, κ ∈ X → κ.is_cardinal) : X.Union.is_cardinal :=
begin
  rw ←init_iff_card, refine ⟨Union_ords_is_ord _, _⟩,
    intros κ κX, exact card_is_ord (Xcard κX),
  simp only [mem_Union, exists_prop], rintro ⟨α, ⟨κ, κX, ακ⟩, Xα⟩,
  have κinit := Xcard κX, rw ←init_iff_card at κinit, apply κinit.right,
  refine ⟨_, ακ, _⟩,
  have αord := ord_of_mem_ord κinit.left ακ,
  replace ακ : α ⊆ κ, rw ←ord_le_iff_sub αord κinit.left, left, exact ακ,
  apply equin_of_dom_of_dom,
    apply dominated_of_equin_of_dominated equin_refl Xα,
    apply dominated_sub (subset_Union_of_mem κX),
  exact dominated_sub ακ,
end

lemma Aleph_oto {α : Set} (αord : α.is_ordinal)
  {β : Set} (βα : β ∈ α) {γ : Set} (γα : γ ∈ α) (fβγ : β.Aleph = γ.Aleph) : β = γ :=
begin
  have βord := (ord_of_mem_ord αord βα),
  have γord := (ord_of_mem_ord αord γα),
  apply ord_eq_of_not_lt βord γord,
    intro βγ, exact (Aleph_lt_of_mem γord βγ).right fβγ,
  intro γβ, exact (Aleph_lt_of_mem βord γβ).right fβγ.symm,
end

lemma Aleph_limit_ord_eq {γ : Set} (γord : γ.limit_ord) : γ.Aleph = (repl_img Aleph γ).Union :=
begin
  have γcard := Aleph_is_card γord.ord,
  have Ucard : (repl_img Aleph γ).Union.is_cardinal, apply Union_card_is_card,
    intro κ, rw mem_repl_img, rintro ⟨β, βγ, κβ⟩, subst κβ,
    exact Aleph_is_card (ord_of_mem_ord γord.ord βγ),
  apply card_eq_of_le_of_le γcard Ucard,
    apply Aleph_least γord.ord Ucard,
      rw [←card_of_cardinal_eq_self Ucard, card_finite_iff_finite],
      refine inf_of_sup_inf (repl_img_inf_of_inf (limit_ord_inf γord) (@Aleph_oto _ γord.ord)) _,
      intro κ, dsimp, simp only [mem_repl_img, mem_Union, exists_prop],
      rintro ⟨α, αγ, κα⟩, subst κα,
      have αord := ord_of_mem_ord γord.ord αγ,
      refine ⟨_, ⟨_, succ_mem_limit γord αγ, rfl⟩, _⟩,
      rw ←card_lt_iff_mem (Aleph_is_card αord) (Aleph_is_card (succ_ord_of_ord αord)),
      exact Aleph_lt_of_mem (succ_ord_of_ord (ord_of_mem_ord γord.ord αγ)) self_mem_succ,
    intros α αγ he,
    have αord := ord_of_mem_ord γord.ord αγ,
    apply ord_mem_irrefl (card_is_ord (Aleph_is_card αord)),
    nth_rewrite 1 ←he, simp only [mem_Union, mem_repl_img, exists_prop],
    refine ⟨_, ⟨_, succ_mem_limit γord αγ, rfl⟩, _⟩,
    rw ←card_lt_iff_mem (Aleph_is_card αord) (Aleph_is_card (succ_ord_of_ord αord)),
    exact Aleph_lt_of_mem (succ_ord_of_ord (ord_of_mem_ord γord.ord αγ)) self_mem_succ,
  rw [card_le_iff_le Ucard γcard, ord_le_iff_sub (card_is_ord Ucard) (card_is_ord γcard)],
  intro α, simp only [mem_Union, exists_prop, mem_repl_img],
  rintro ⟨κ, ⟨β, βγ, κβ⟩, ακ⟩, subst κβ, apply ord_mem_trans (card_is_ord γcard) ακ,
  have βord := ord_of_mem_ord γord.ord βγ,
  rw ←card_lt_iff_mem (Aleph_is_card βord) γcard,
  exact Aleph_lt_of_mem γord.ord βγ,
end

noncomputable def beth_fun : Set → Set := (fun f,
  if f.dom = ∅
    then card ω
  else if ex₁ : ∃ α : Set, α.is_ordinal ∧ f.dom = α.succ
    then card_exp two (f.fun_value (classical.some ex₁))
  else if ex₂ : ∃ γ : Set, γ.limit_ord ∧ f.dom = γ
    then f.ran.Union
  else ∅)
lemma beth_fun_empty {f : Set} (fdom : f.dom = ∅) : beth_fun f = card ω :=
begin
  rw beth_fun, dsimp, rw if_pos fdom,
end
lemma beth_fun_succ {f α : Set} (αord : α.is_ordinal) (dom : f.dom = α.succ) :
  beth_fun f = two.card_exp (f.fun_value α) :=
begin
  have h : ¬ f.dom = ∅, rw [eq_empty, dom], push_neg, exact ⟨_, self_mem_succ⟩,
  rw beth_fun, dsimp, rw if_neg h,
  have ex₁ : ∃ α : Set, α.is_ordinal ∧ f.dom = α.succ := ⟨_, αord, dom⟩,
  rw dif_pos ex₁,
  obtain ⟨ord, dom'⟩ := classical.some_spec ex₁, rw dom' at dom,
  have h₂ := succ_inj' dom, rw h₂,
end
lemma beth_fun_limit {f γ : Set} (γord : γ.limit_ord) (dom : f.dom = γ) :
  beth_fun f = f.ran.Union :=
begin
  have ex₀ : ¬ f.dom = ∅, rw dom, exact γord.ne,
  have ex₁ : ¬ ∃ α : Set, α.is_ordinal ∧ f.dom = α.succ,
    rw dom, rintro ⟨α, -, γα⟩, exact γord.ns ⟨_, γα⟩,
  have ex₂ : ∃ γ : Set, γ.limit_ord ∧ f.dom = γ := ⟨_, γord, dom⟩,
  rw beth_fun, dsimp, rw [if_neg ex₀, dif_neg ex₁, if_pos ex₂],
end
noncomputable def beth : Set → Set := ord_rec beth_fun
lemma beth_zero : beth ∅ = card ω :=
begin
  have dom : (con_fun beth_fun ∅).dom = ∅ := con_fun_dom zero_is_ord,
  rw [beth, ord_rec_spec zero_is_ord, beth_fun_empty dom], 
end
lemma beth_succ {α : Set} (αord : α.is_ordinal) : beth α.succ = card_exp two α.beth :=
begin
  have αord' := succ_ord_of_ord αord,
  rw [beth, ord_rec_spec αord', beth_fun_succ αord (con_fun_dom αord'), con_fun_spec αord' self_mem_succ],
end
lemma beth_limit {γ : Set} (γord : γ.limit_ord) : beth γ = (repl_img beth γ).Union :=
begin
  rw [beth, ord_rec_spec γord.ord, beth_fun_limit γord (con_fun_dom γord.ord)], apply ext,
  have h : ∀ {x z : Set}, x ∈ γ ∧ z = (con_fun beth_fun γ).fun_value x ↔ x ∈ γ ∧ z = ord_rec beth_fun x :=
    λ x z, and_congr_right (λ xγ, eq.congr_right (con_fun_spec γord.ord xγ)),
  simp only [mem_Union, exists_prop, mem_repl_img, mem_ran_iff (con_fun_fun γord.ord), con_fun_dom γord.ord, h, forall_const, iff_self],
end

lemma beth_is_card {α : Set} (αord : α.is_ordinal) : α.beth.is_cardinal :=
begin
  revert α, apply trans_ind_schema, intros α αord ind,
  by_cases αe : α = ∅,
    subst αe, rw beth_zero, exact ⟨_, rfl⟩,
  by_cases αs : ∃ β : Set, α = β.succ,
    rcases αs with ⟨β, αβ⟩, subst αβ,
    rw beth_succ (ord_of_succ_ord αord),
    apply exp_cardinal (nat_is_cardinal two_nat) (ind self_mem_succ),
  replace αord : α.limit_ord := ⟨αord, αe, αs⟩,
  rw beth_limit αord, apply Union_card_is_card, intro κ,
  rw mem_repl_img, rintro ⟨β, βα, κβ⟩, subst κβ, exact ind βα,
end

lemma beth_is_ord {α : Set} (αord : α.is_ordinal) : α.beth.is_ordinal := card_is_ord (beth_is_card αord)

def continuum_hypothesis : Prop := one.Aleph = one.beth
def generalized_continuum_hypothesis : Prop := ∀ α : Set, α.is_ordinal → α.Aleph = α.beth

def ord_op (f : Set → Set) : Prop := ∀ ⦃α : Set⦄, α.is_ordinal → (f α).is_ordinal
def monotone (f : Set → Set) : Prop := ∀ ⦃β : Set⦄, β.is_ordinal → ∀ {α : Set}, α ∈ β → f α ∈ f β
def continuous (f : Set → Set) : Prop := ∀ ⦃γ : Set⦄, γ.limit_ord → f γ = (repl_img f γ).Union
structure normal (f : Set → Set) : Prop :=
(mon : monotone f)
(con : continuous f)

theorem omega_limit_ord : limit_ord nat.{u} :=
begin
  refine ⟨omega_is_ord, _, _⟩,
    apply ne_empty_of_inhabited, refine ⟨_, zero_nat⟩,
  rintro ⟨α, ωα⟩,
  have αω : α ∈ nat.{u}, rw ωα, exact self_mem_succ,
  have αω' := nat_induct.succ_closed αω,
  rw ωα at αω', exact nat_not_mem_self (nat_induct.succ_closed αω) αω',
end

theorem Union_succ_limit {γ : Set} (γord : γ.limit_ord) : (repl_img succ γ).Union = γ :=
begin
  apply ext, simp only [mem_Union, exists_prop, mem_repl_img], intro α, split,
    rintro ⟨β', ⟨β, βγ, ββ'⟩, αβ⟩, subst ββ', rw [succ, mem_union, mem_singleton] at αβ, cases αβ,
      subst αβ, exact βγ,
    exact ord_mem_trans γord.ord αβ βγ,
  intro αγ, exact ⟨_, ⟨_, αγ, rfl⟩, self_mem_succ⟩,
end

lemma succ_monotone : monotone succ := λ β βord α αβ, mem_succ_iff_le.mpr (succ_least_upper_bound βord αβ)
lemma not_succ_continuous : ¬ continuous succ :=
begin
  rw continuous, push_neg, refine ⟨_, omega_limit_ord, _⟩,
  rw Union_succ_limit omega_limit_ord, exact self_ne_succ,
end

lemma Aleph_ord_op : ord_op Aleph :=
λ α αord, card_is_ord (Aleph_is_card αord)

lemma Aleph_normal : normal Aleph :=
begin
  refine ⟨λ β βord α αβ, _, @Aleph_limit_ord_eq⟩,
  have αord := ord_of_mem_ord βord αβ,
  rw ←card_lt_iff_mem (Aleph_is_card αord) (Aleph_is_card βord),
  exact Aleph_lt_of_mem βord αβ,
end

def sup (S : Set) : Set := S.Union

lemma cont_iff {f : Set → Set} : continuous f ↔ ∀ {γ : Set}, γ.limit_ord → f γ = (repl_img f γ).sup := iff.rfl

lemma fun_le {f : Set → Set} {a b : Set} (h₁ : a ∈ b → f a ∈ f b) (h₂ : a ≤ b) : f a ≤ f b :=
begin
  cases h₂,
    exact or.inl (h₁ h₂),
  subst h₂, exact or.inr rfl,
end

-- Theorem Schema 8C
theorem mon_of_con {f : Set → Set} (ford : ord_op f) (con : continuous f) 
  (h : ∀ {γ : Set}, γ.is_ordinal → f γ ∈ f γ.succ) : monotone f :=
begin
  intros β βord α αβ,
  have αord := ord_of_mem_ord βord αβ,
  revert β βord, refine trans_ind_schema _, intros β βord ind αβ, by_cases βe : β = ∅,
    subst βe, exfalso, exact mem_empty _ αβ,
  by_cases βγ : ∃ γ : Set, β = γ.succ,
    rcases βγ with ⟨γ, βγ⟩, subst βγ,
    refine ord_lt_of_le_of_lt (ford βord) _ (h (ord_of_succ_ord βord)),
    apply fun_le (ind self_mem_succ), rw ←mem_succ_iff_le, exact αβ,
  replace βord : β.limit_ord := ⟨βord, βe, βγ⟩,
  have αβ' : α.succ ∈ β := succ_mem_limit βord αβ,
  simp only [con βord, mem_Union, exists_prop, mem_repl_img],
  exact ⟨_, ⟨_, αβ', rfl⟩, ind αβ' self_mem_succ⟩,
end

theorem norm_of_con {f : Set → Set} (ford : ord_op f) (con : continuous f)
  (h : ∀ {γ : Set}, γ.is_ordinal → f γ ∈ f γ.succ) : normal f :=
⟨mon_of_con @ford con @h, con⟩

theorem beth_norm : normal beth :=
begin
  apply norm_of_con @beth_is_ord @beth_limit,
  intros γ γord,
  rw [←card_lt_iff_mem (beth_is_card γord) (beth_is_card (succ_ord_of_ord γord)), beth_succ γord],
  exact card_lt_exp (beth_is_card γord),
end

lemma le_norm_fun {f : Set → Set} (ford : ord_op f) (norm : normal f) {α : Set} (αord : α.is_ordinal) : α ≤ f α :=
begin
  revert α, apply trans_ind_schema, intros α αord ind,
  by_cases αe : α = ∅,
    subst αe, rw ord_le_iff_sub zero_is_ord (ford zero_is_ord), exact empty_subset,
  by_cases αs : ∃ β : Set, α = β.succ,
    rcases αs with ⟨β, αβ⟩, subst αβ,
    apply succ_least_upper_bound (ford αord),
    apply ord_lt_of_le_of_lt (ford αord) (ind self_mem_succ) (norm.mon αord self_mem_succ),
  replace αord : α.limit_ord := ⟨αord, αe, αs⟩,
  rw [ord_le_iff_sub αord.ord (ford αord.ord), norm.con αord], intros β βα,
  simp only [mem_Union, exists_prop, mem_repl_img], refine ⟨_, ⟨_, succ_mem_limit αord βα, rfl⟩, _⟩,
  have βord : β.succ.is_ordinal := succ_ord_of_ord (ord_of_mem_ord αord.ord βα),
  apply ord_lt_of_le_of_lt (ford βord) (ind βα) (norm.mon βord self_mem_succ),
end

lemma is_succ_of_not_zero_of_not_limit {α : Set} (αord : α.is_ordinal) (αe : α ≠ ∅) (αnl : ¬ α.limit_ord) : ∃ β : Set, α = β.succ :=
classical.by_contradiction (λ h, αnl ⟨αord, αe, h⟩)

-- Theorem Schema 8D
theorem exists_large_ord_of_norm {f : Set → Set} (ford : ord_op f) (norm : normal f)
  {β : Set} (βord : β.is_ordinal) (βl : f ∅ ≤ β) : ∃ γ : Set, γ.is_ordinal ∧ f γ ≤ β ∧ ∀ {α : Set}, α.is_ordinal → f α ≤ β → α ≤ γ :=
begin
  let X : Set := {α ∈ β.succ | α.is_ordinal ∧ f α ≤ β},
  have memX : ∀ {α : Set}, α ∈ X ↔ α.is_ordinal ∧ f α ≤ β, simp only [mem_sep, and_iff_right_iff_imp, and_imp],
    intros α αord αβ, rw mem_succ_iff_le, exact ord_le_trans βord (le_norm_fun ford norm αord) αβ,
  have Xord : X.is_ordinal, apply trans_ords_is_ord,
      intros α αX, rw memX at αX, exact αX.left,
    rw transitive_set_iff, intros α αX γ γα, rw memX at αX ⊢, refine ⟨ord_of_mem_ord αX.left γα, _⟩,
    left, apply ord_lt_of_lt_of_le βord (norm.mon αX.left γα), exact αX.right,
  suffices h : ∃ γ : Set, X = γ.succ,
    rcases h with ⟨γ, Xγ⟩,
    have γord : γ.is_ordinal, apply ord_of_succ_ord, rw ←Xγ, exact Xord,
    have γX : γ ∈ X, rw Xγ, exact self_mem_succ,
    rw memX at γX,
    refine ⟨_, γord, γX.right, λ α αord αβ, _⟩, rw [←mem_succ_iff_le, ←Xγ, memX],
    exact ⟨αord, αβ⟩,
  apply is_succ_of_not_zero_of_not_limit Xord,
    apply ne_empty_of_inhabited, use ∅, rw memX,
    exact ⟨zero_is_ord, βl⟩,
  intro Xl, apply ord_mem_irrefl Xord, rw memX, refine ⟨Xord, _⟩,
  rw [ord_le_iff_sub (ford Xord) βord, norm.con Xl], intro γ,
  simp only [mem_Union, exists_prop, mem_repl_img],
  rintro ⟨fα, ⟨α, αX, fαα⟩, γfα⟩, subst fαα, rw memX at αX,
  exact ord_lt_of_lt_of_le βord γfα αX.right,
end

lemma exists_larger_of_not_bounded {S : Set} (Sord : ∀ {α : Set}, α ∈ S → α.is_ordinal)
  (h : ¬ ∃ β : Set, β ∈ S ∧ ∀ {α : Set}, α ∈ S → α ≤ β) {α : Set} (αS : α ∈ S) : ∃ β : Set, β ∈ S ∧ α ∈ β :=
begin
  apply classical.by_contradiction, intro h₁, push_neg at h₁, apply h, refine ⟨_, αS, _⟩,
  intros β βS, rw ←ord_not_lt_iff_le (Sord αS) (Sord βS), exact h₁ _ βS,
end

lemma repl_img_ords {f : Set → Set} (ford : ord_op f) {S : Set} (Sord : ∀ {α : Set}, α ∈ S → α.is_ordinal) :
  ∀ ⦃α : Set⦄, α ∈ (repl_img f S) → α.is_ordinal :=
begin
  intros α, rw mem_repl_img, rintro ⟨β, βS, αβ⟩, subst αβ, exact ford (Sord βS),
end

-- Theorem Schema 8E
theorem sup_norm_fun {f : Set → Set} (ford : ord_op f) (norm : normal f)
  {S : Set} (Sne : S ≠ ∅) (Sord : ∀ {α : Set}, α ∈ S → α.is_ordinal) : f S.sup = (repl_img f S).sup :=
begin
  have SU := Union_ords_is_ord @Sord,
  have h₁ := ford SU,
  have h₂ : (repl_img f S).Union.is_ordinal, apply Union_ords_is_ord, intro α,
    rw mem_repl_img, rintro ⟨β, βS, αβ⟩, subst αβ, exact ford (Sord βS),
  simp only [sup], rw ord_eq_iff_le_and_le h₁ h₂, split,
    by_cases h₃ : ∃ β : Set, β ∈ S ∧ ∀ {α : Set}, α ∈ S → α ≤ β,
      obtain ⟨SUS, Ub⟩ := case_exists_bound @Sord h₃,
      rw ord_le_iff_sub h₁ h₂, apply subset_Union_of_mem, rw mem_repl_img,
      exact ⟨_, SUS, rfl⟩,
    have USne : S.Union ≠ ∅, apply ne_empty_of_inhabited,
      obtain ⟨α, αS⟩ := inhabited_of_ne_empty Sne,
      obtain ⟨β, βS, αβ⟩ := exists_larger_of_not_bounded @Sord h₃ αS,
      use α, simp only [mem_Union, exists_prop], exact ⟨_, βS, αβ⟩,
    have Slim : S.Union.limit_ord, refine ⟨SU, USne, (case_not_exists_bound @Sord h₃).right⟩,
    have h : (repl_img f S.Union).Union.is_ordinal := Union_ords_is_ord (repl_img_ords ford (ord_of_mem_ord SU)),
    rw norm.con Slim, rw ord_le_iff_sub h h₂, intro β, simp only [mem_Union, exists_prop, mem_repl_img],
    rintro ⟨fα, ⟨α, ⟨γ, γS, αγ⟩, fαα⟩, βfα⟩, subst fαα, refine ⟨_, ⟨_, γS, rfl⟩, _⟩,
    apply ord_mem_trans (ford (Sord γS)) βfα, exact norm.mon (Sord γS) αγ,
  rw ord_le_iff_sub h₂ h₁, intro β, rw mem_Union, simp only [exists_prop, mem_repl_img],
  rintro ⟨fα, ⟨α, αS, fαα⟩, βfα⟩, subst fαα,
  apply ord_lt_of_lt_of_le h₁ βfα, apply fun_le (norm.mon SU),
  rw ord_le_iff_sub (Sord αS) SU, exact subset_Union_of_mem αS,
end

-- Veblen Fixed-Point Theorem Schema
theorem exists_fixed_point {f : Set → Set} (ford : ord_op f) (norm : normal f)
  {β : Set.{u}} (βord : β.is_ordinal) : ∃ γ : Set, γ.is_ordinal ∧ f γ = γ ∧ β ≤ γ :=
begin
  cases le_norm_fun ford norm βord with ββ ββ,
    let F := rec_fun' f β,
    let μ := F.ran.sup,
    use μ,
    have rne : F.ran ≠ ∅, rw [ne.def, ←dom_ran_eq_empty_iff, rec_fun_dom'],
      apply ne_empty_of_inhabited, exact ⟨_, zero_nat⟩,
    have rord : ∀ {n : Set}, n ∈ nat.{u} → (F.fun_value n).is_ordinal,
      apply induction,
        rw rec_fun_base', exact βord,
      intros n nω ind, rw rec_fun_ind' nω, exact ford ind,
    have rord' : ∀ {α : Set}, α ∈ F.ran → α.is_ordinal, intro α,
      rw [mem_ran_iff (rec_fun_fun'), rec_fun_dom'], rintro ⟨n, nω, αn⟩, subst αn,
      exact rord nω,
    have μord : μ.is_ordinal := Union_ords_is_ord @rord',
    have μne : μ ≠ ∅, apply ne_empty_of_inhabited, use β,
      change β ∈ F.ran.Union, simp only [mem_Union, exists_prop, mem_ran_iff rec_fun_fun', rec_fun_dom'],
      refine ⟨_, ⟨succ ∅, one_nat, rfl⟩, _⟩, rw [rec_fun_ind' zero_nat, rec_fun_base'],
      exact ββ,
    have Fmem : ∀ {n : Set}, n ∈ nat.{u} → F.fun_value n ∈ F.fun_value n.succ,
      apply induction,
        rw [rec_fun_ind' zero_nat, rec_fun_base'], exact ββ,
      intros n nω ind,
      have nω' : n.succ ∈ nat.{u} := nat_induct.succ_closed nω,
      rw [rec_fun_ind' nω, rec_fun_ind' nω'],
      exact norm.mon (rord nω') ind,
    have μlim : μ.limit_ord, apply limit_ord_of_not_bound μord μne, push_neg,
      intros α αμ, change α ∈ F.ran.Union at αμ,
      simp only [mem_Union, exists_prop, mem_ran_iff rec_fun_fun', rec_fun_dom'] at αμ,
      rcases αμ with ⟨Fn, ⟨n, nω, Fnn⟩, αFn⟩, subst Fnn, use F.fun_value n,
      rw ord_not_le_iff_lt (rord nω) (ord_of_mem_ord (rord nω) αFn),
      change F.fun_value n ∈ F.ran.Union ∧ α ∈ F.fun_value n,
      simp only [mem_Union, exists_prop, mem_ran_iff rec_fun_fun', rec_fun_dom'],
      exact ⟨⟨_, ⟨_, nat_induct.succ_closed nω, rfl⟩, Fmem nω⟩, αFn⟩,
    refine ⟨μlim.ord, _, _⟩,
      change f μ = F.ran.sup,
      rw [sup_norm_fun ford norm rne @rord', sup, sup], rw eq_iff_subset_and_subset, split,
        apply Union_sub_of_sub, apply repl_img_sub_of_closed, intro α,
        simp only [mem_ran_iff rec_fun_fun', rec_fun_dom'], rintro ⟨n, nω, αFn⟩, subst αFn,
        exact ⟨_, nat_induct.succ_closed nω, (rec_fun_ind' nω).symm⟩,
      intro α, simp only [mem_Union, exists_prop, mem_repl_img, mem_ran_iff rec_fun_fun', rec_fun_dom'],
      rintro ⟨Fn, ⟨n, nω, Fnn⟩, αFn⟩, subst Fnn,
      refine ⟨_, ⟨_, ⟨_, nω, rfl⟩, rfl⟩, _⟩, rw ←@rec_fun_ind' f β _ nω,
      exact ord_mem_trans (rord (nat_induct.succ_closed nω)) αFn (Fmem nω),
    rw ord_le_iff_sub βord μord, apply subset_Union_of_mem,
    rw [mem_ran_iff rec_fun_fun', rec_fun_dom'], refine ⟨_, zero_nat, _⟩,
    rw rec_fun_base',
  exact ⟨_, βord, ββ.symm, or.inr rfl⟩,
end

-- the exercises for ordinal operations section are pretty good

-- exercise 3
theorem mon_op_mon_iff {f : Set → Set} (ford : ord_op f) (mon : monotone f)
  {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) : α ∈ β ↔ f α ∈ f β :=
⟨λ αβ, mon βord αβ, λ fαβ, begin
  apply classical.by_contradiction, intro βα, rw ord_not_lt_iff_le αord βord at βα,
  cases βα,
    exact ord_mem_irrefl (ford βord) (ord_mem_trans (ford βord) (mon αord βα) fαβ),
  subst βα, exact ord_mem_irrefl (ford βord) fαβ,
end⟩

theorem mon_op_inj {f : Set → Set} (ford : ord_op f) (mon : monotone f)
  {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) (h : f α = f β) : α = β :=
begin
  apply classical.by_contradiction, intro eq,
  cases ord_conn αord βord eq with αβ βα,
    have h₂ := mon βord αβ, rw h at h₂, apply ord_mem_irrefl (ford βord) h₂,
  have h₂ := mon αord βα, rw h at h₂, apply ord_mem_irrefl (ford βord) h₂,
end

theorem mon_op_le_iff {f : Set → Set} (ford : ord_op f) (mon : monotone f)
  {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) : α ≤ β ↔ f α ≤ f β :=
⟨λ h, or.elim h (λ h₁, by left; rwa ←mon_op_mon_iff ford mon αord βord) (λ h₁, by right; rw h₁),
λ h, or.elim h (λ h₁, by left; rwa mon_op_mon_iff ford mon αord βord) (λ h₁, or.inr (mon_op_inj ford mon αord βord h₁))⟩

def struct_to_set (R : struct) : Set := R.fld.pair R.rel
lemma struct_to_set_is_pair {R : struct} : (struct_to_set R).is_pair := ⟨_, _, rfl⟩
def empty_struct : struct := ⟨∅, ∅, λ p hp, begin rw prod_empty_eq_empty, exact hp, end⟩
noncomputable def set_to_struct (R : Set) : struct := if is_rel : R.snd ⊆ R.fst.prod R.fst then ⟨R.fst, R.snd, is_rel⟩ else empty_struct
lemma set_fst_eq_fld {R : struct} : (struct_to_set R).fst = R.fld := by rw [struct_to_set, fst_congr]
lemma set_snd_eq_rel {R : struct} : (struct_to_set R).snd = R.rel := by rw [struct_to_set, snd_congr]
lemma set_rel {R : struct} : (struct_to_set R).snd ⊆ (struct_to_set R).fst.prod (struct_to_set R).fst :=
begin
  rw [struct_to_set, fst_congr, snd_congr], exact R.is_rel,
end
lemma fld_eq_set_fst {R : Set} (is_rel : R.snd ⊆ R.fst.prod R.fst) : (set_to_struct R).fld = R.fst := by rw [set_to_struct, dif_pos is_rel]
lemma rel_eq_set_snd {R : Set} (is_rel : R.snd ⊆ R.fst.prod R.fst) : (set_to_struct R).rel = R.snd := by rw [set_to_struct, dif_pos is_rel]
lemma struct_set_struct_eq_self (R : struct) : set_to_struct (struct_to_set R) = R :=
begin
  ext,
    rw [fld_eq_set_fst set_rel], exact set_fst_eq_fld,
  rw [rel_eq_set_snd set_rel], exact set_snd_eq_rel,
end
lemma struct_to_set_oto {R S : struct} (RS : struct_to_set R = struct_to_set S) : R = S :=
begin
  ext,
    rw [←set_fst_eq_fld, ←set_fst_eq_fld, RS],
  rw [←set_snd_eq_rel, ←set_snd_eq_rel, RS],
end
lemma set_struct_set_eq_self {R : Set} (Rpair : R.is_pair) (is_rel : R.snd ⊆ R.fst.prod R.fst) :
  struct_to_set (set_to_struct R) = R :=
begin
  apply pair_eq struct_to_set_is_pair Rpair,
    rw [set_fst_eq_fld, fld_eq_set_fst is_rel],
  rw [set_snd_eq_rel, rel_eq_set_snd is_rel],
end

noncomputable def str_rank (R : struct) : Set := rank (struct_to_set R)
lemma str_rank_ord {R : struct} : (str_rank R).is_ordinal := rank_ord_of_grounded all_grounded
def pioneering (R : struct) : Prop := ¬ ∃ S : struct, isomorphic R S ∧ str_rank S ∈ str_rank R
lemma exists_rank_iso_struct (R : struct) :
  ∃ α : Set, α.is_ordinal ∧ ∃ S : struct, isomorphic R S ∧ α = str_rank S :=
⟨_, rank_ord_of_grounded all_grounded, _, iso_refl, rfl⟩
noncomputable def pioneering_ord (R : struct) : Set := classical.some (exists_least_ord_of_exists (exists_rank_iso_struct R))
lemma pioneering_ord_spec (R : struct) : (pioneering_ord R).is_ordinal ∧ (∃ S : struct, isomorphic R S ∧ pioneering_ord R = str_rank S)
  ∧ ∀ {β : Set}, β.is_ordinal → (∃ S : struct, isomorphic R S ∧ β = str_rank S) → pioneering_ord R ≤ β :=
classical.some_spec (exists_least_ord_of_exists (exists_rank_iso_struct R))

lemma pioneering_ord_ord {R : struct} : (pioneering_ord R).is_ordinal :=
begin
  obtain ⟨ord, -, -⟩ := @pioneering_ord_spec R, exact ord,
end
lemma exists_iso_of_pioneering_rank {R : struct} : ∃ S : struct, isomorphic R S ∧ pioneering_ord R = str_rank S :=
begin
  obtain ⟨-, h, -⟩ := @pioneering_ord_spec R, exact h,
end
lemma pioneering_ord_least {R S : struct} (RS : isomorphic R S) : pioneering_ord R ≤ str_rank S :=
begin
  obtain ⟨-, -, least⟩ := @pioneering_ord_spec R,
  exact least (rank_ord_of_grounded all_grounded) ⟨_, RS, rfl⟩,
end
lemma rank_iso_pioneering_iff {R S : struct} (RS : isomorphic R S) : pioneering S ↔ pioneering_ord R = str_rank S :=
begin
  split,
  { intro Sp,
    rw [str_rank, ord_eq_iff_le_and_le pioneering_ord_ord (rank_ord_of_grounded all_grounded)], split,
      exact pioneering_ord_least RS,
    rw ←ord_not_lt_iff_le pioneering_ord_ord (rank_ord_of_grounded all_grounded), intro h, apply Sp,
    obtain ⟨T, RT, RT'⟩ := @exists_iso_of_pioneering_rank R,
    rw RT' at h, exact ⟨_, iso_trans (iso_symm RS) RT, h⟩, },
  { rintros RS' ⟨T, ST, TS⟩, revert TS, change str_rank T ∉ str_rank S,
    rw [ord_not_lt_iff_le str_rank_ord str_rank_ord, ←RS'],
    exact pioneering_ord_least (iso_trans RS ST), },
end
lemma rank_eq_of_iso_pioneering {R S : struct} (RS : isomorphic R S) (Rp : pioneering R) (Sp : pioneering S) :
  str_rank R = str_rank S :=
begin
  rw [←(rank_iso_pioneering_iff (iso_symm RS)).mp Rp, ←rank_iso_pioneering_iff iso_refl], exact Sp,
end

lemma rank_eq_of_le_iso_pioneering {R S : struct} (RS : isomorphic S R)
  (Sp : pioneering S) (RleS : str_rank R ≤ str_rank S) : str_rank S = str_rank R :=
begin
  symmetry,
  rw ord_eq_iff_le_and_le str_rank_ord str_rank_ord, refine ⟨RleS, _⟩,
  rw rank_iso_pioneering_iff (iso_symm RS) at Sp, rw ←Sp,
  exact pioneering_ord_least iso_refl,
end

noncomputable def it (R : struct.{u}) : Set.{u} :=
{S ∈ (pioneering_ord R).succ.Veb | ∃ T : struct, S = struct_to_set T ∧ pioneering T ∧ isomorphic R T}

lemma mem_it {R : struct} {S : Set} : S ∈ it R ↔ ∃ T : struct, S = struct_to_set T ∧ pioneering T ∧ isomorphic R T :=
begin
  simp only [it, mem_sep, and_imp, and_iff_right_iff_imp, exists_imp_distrib],
  intros T ST Tp RT, subst ST,
  rw [(rank_iso_pioneering_iff RT).mp Tp, str_rank, Veb_succ_eq_powerset (rank_ord_of_grounded all_grounded), mem_powerset],
  exact rank_sub_of_grounded all_grounded,
end

lemma struct_mem_it {R S : struct} : struct_to_set S ∈ it R ↔ pioneering S ∧ isomorphic R S :=
by simp only [mem_it, struct_set_struct_eq_self, function.injective.eq_iff @struct_to_set_oto, exists_eq_left']

lemma it_inhab (R : struct) : (it R).inhab :=
begin
  obtain ⟨S, RS, RS'⟩ := @exists_iso_of_pioneering_rank R,
  use struct_to_set S, rw ←rank_iso_pioneering_iff RS at RS', rw mem_it,
  exact ⟨_, rfl, RS', RS⟩,
end

-- Theorem 8F
theorem iso_type_eq_iff_iso {R S : struct} : it R = it S ↔ isomorphic R S :=
begin
  split,
  { intro RS,
    obtain ⟨C, CR⟩ := it_inhab R,
    have CS : C ∈ it S, rw ←RS, exact CR,
    rw mem_it at CR, rcases CR with ⟨T, CT, -, RT⟩,
    rw mem_it at CS, rcases CS with ⟨U, CU, -, SU⟩,
    have TU : T = U, rw [←struct_set_struct_eq_self T, ←struct_set_struct_eq_self U, ←CT, ←CU],
    subst TU, exact iso_trans RT (iso_symm SU), },
  { revert R S,
    have sub : ∀ {R S : struct}, isomorphic R S → it R ⊆ it S,
      intros R S RS C, simp only [mem_it],
      rintro ⟨T, CT, Tp, RT⟩, exact ⟨_, CT, Tp, iso_trans (iso_symm RS) RT⟩,
    intros R S, rw eq_iff_subset_and_subset,
    exact λ RS, ⟨sub RS, sub (iso_symm RS)⟩, },
end

def order_type (ρ : Set) : Prop := ∃ R : struct, R.fld.lin_order R.rel ∧ ρ = it R

lemma order_type_inhab {ρ : Set} (ρot : ρ.order_type) : ρ.inhab :=
begin
  rcases ρot with ⟨R, Rlin, ρR⟩, subst ρR, exact it_inhab R,
end

lemma mem_order_type {ρ : Set} (ρot : ρ.order_type) {R : Set} (Rρ : R ∈ ρ)
  {S : Set} : S ∈ ρ ↔ ∃ T : struct, S = struct_to_set T ∧ str_rank (set_to_struct R) = str_rank T ∧ isomorphic (set_to_struct R) T ∧ T.fld.lin_order T.rel :=
begin
  rcases ρot with ⟨U, Ulin, ρU⟩, subst ρU, rw mem_it at Rρ ⊢,
  rcases Rρ with ⟨V, RV, Vp, UV⟩, subst RV, split,
  { rintro ⟨T, ST, Tp, UT⟩, subst ST, refine ⟨_, rfl, _, _, lin_order_iso UT Ulin⟩,
      rw struct_set_struct_eq_self V,
      have VT := iso_trans (iso_symm UV) UT,
      rw rank_iso_pioneering_iff VT at Tp, rw ←Tp,
      symmetry, rw ←rank_iso_pioneering_iff iso_refl, exact Vp,
    rw struct_set_struct_eq_self V,
    exact iso_trans (iso_symm UV) UT, },
  { rintro ⟨T, ST, VT, VT', Tlin⟩, subst ST,
    rw struct_set_struct_eq_self V at VT',
    refine ⟨_, rfl, _, iso_trans UV VT'⟩,
    rw struct_set_struct_eq_self V at VT,
    rw [rank_iso_pioneering_iff VT', ←VT, ←rank_iso_pioneering_iff iso_refl], exact Vp, },
end

lemma struct_mem_order_type {ρ : Set} (ρot : ρ.order_type) {R : struct} (Rρ : struct_to_set R ∈ ρ)
  {S : struct} : struct_to_set S ∈ ρ ↔ str_rank R = str_rank S ∧ isomorphic R S ∧ S.fld.lin_order S.rel :=
by simp only [mem_order_type ρot Rρ, struct_set_struct_eq_self, function.injective.eq_iff @struct_to_set_oto, exists_eq_left']

lemma of_mem_order_type {ρ : Set} (ρot : ρ.order_type) {R : Set} (Rρ : R ∈ ρ) :
  ∃ T : struct, R = struct_to_set T ∧ pioneering T ∧ T.fld.lin_order T.rel :=
begin
  rcases ρot with ⟨S, Slin, ρS⟩, subst ρS,
  rw mem_it at Rρ, rcases Rρ with ⟨T, RT, Tp, ST⟩, subst RT,
  exact ⟨_, rfl, Tp, lin_order_iso ST Slin⟩,
end

lemma order_type_ext {ρ : Set} (ρot : ρ.order_type) {R : struct} (Rρ : struct_to_set R ∈ ρ)
  {σ : Set} (σot : σ.order_type) {S : struct} (Sσ : struct_to_set S ∈ σ)
  (h : ∀ {T : struct}, struct_to_set T ∈ ρ ↔ struct_to_set T ∈ σ) : ρ = σ :=
begin
  apply ext, intro T, rw [mem_order_type ρot Rρ, mem_order_type σot Sσ], split,
    rintro ⟨U, TU, rank, iso, lin⟩, subst TU, rw struct_set_struct_eq_self at rank iso ⊢,
    simp only [struct_set_struct_eq_self, function.injective.eq_iff @struct_to_set_oto, exists_eq_left'],
    rw [←struct_mem_order_type σot Sσ, ←h, struct_mem_order_type ρot Rρ],
    exact ⟨rank, iso, lin⟩,
  rintro ⟨U, TU, rank, iso, lin⟩, subst TU, rw struct_set_struct_eq_self at rank iso ⊢,
  simp only [struct_set_struct_eq_self, function.injective.eq_iff @struct_to_set_oto, exists_eq_left'],
  rw [←struct_mem_order_type ρot Rρ, h, struct_mem_order_type σot Sσ],
  exact ⟨rank, iso, lin⟩,
end

lemma fst_fun_onto {A B : Set} (Bne : B ≠ ∅) : (pair_sep_eq (A.prod B) A fst).onto_fun (A.prod B) A :=
begin
  refine ⟨pair_sep_eq_is_fun, pair_sep_eq_dom_eq _, pair_sep_eq_ran_eq _⟩,
    intro p, rw mem_prod, rintro ⟨a, aA, b, bB, pab⟩, subst pab, rw fst_congr, exact aA,
  intros a aA,
  obtain ⟨b, bB⟩ := inhabited_of_ne_empty Bne,
  use a.pair b, rw [pair_mem_prod, fst_congr], exact ⟨⟨aA, bB⟩, rfl⟩,
end

lemma fst_fun_oto {A x : Set} : (pair_sep_eq (A.prod {x}) A fst).one_to_one :=
begin
  apply pair_sep_eq_oto, intros p hp q hq, rw mem_prod at hp hq,
  rcases hp with ⟨a, aA, b, bB, pab⟩, rcases hq with ⟨a', aA', b', bB', qab⟩, subst pab, subst qab,
  simp only [fst_congr], intro aa, subst aa, apply pair_eq ⟨_, _, rfl⟩ ⟨_, _, rfl⟩,
    simp only [fst_congr],
  simp only [snd_congr], rw mem_singleton at bB bB', rw [bB', bB],
end

lemma fst_fun_value {A x a : Set} (aA : a ∈ A) : (pair_sep_eq (A.prod {x}) A fst).fun_value (a.pair x) = a :=
begin
  have h : a.pair x ∈ (pair_sep_eq (A.prod {x}) A fst).dom,
    rw [(fst_fun_onto singleton_ne_empty).right.left, pair_mem_prod, mem_singleton],
    exact ⟨aA, rfl⟩,
  rw [pair_sep_eq_fun_value h, fst_congr],
end

lemma fst_fun_value' {A x p : Set} (hp : p ∈ A.prod {x}) : (pair_sep_eq (A.prod {x}) A fst).fun_value p = p.fst :=
begin
  rw ←(fst_fun_onto singleton_ne_empty).right.left at hp,
  exact pair_sep_eq_fun_value hp,
end

lemma fst_fun_corr {A x : Set} : correspondence (A.prod {x}) A (pair_sep_eq (A.prod {x}) A fst) :=
⟨fst_fun_onto singleton_ne_empty, fst_fun_oto⟩

lemma fst_fun_iso {R : struct} {x : Set} : isomorphic ⟨R.fld.prod {x}, fun_order (R.fld.prod {x}) R.rel (pair_sep_eq (R.fld.prod {x}) R.fld fst), pair_sep_sub_prod⟩ R :=
begin
  refine ⟨_, fst_fun_corr, _⟩, dsimp, intros y z hy hz,
  simp only [fun_order, pair_mem_pair_sep' hy hz],
end

lemma ex_disj_of_ord_type' {A : struct} (Alin : A.fld.lin_order A.rel) {B : struct} (Blin : B.fld.lin_order B.rel) :
  ∃ P : struct × struct, isomorphic P.fst A ∧ isomorphic P.snd B ∧ P.fst.fld ∩ P.snd.fld = ∅ :=
⟨⟨_, _⟩, fst_fun_iso, fst_fun_iso, disj zero_ne_one⟩

lemma ex_3_disj {A : struct} (Alin : A.fld.lin_order A.rel)
  {B : struct} (Blin : B.fld.lin_order B.rel)
  {C : struct} (Clin : C.fld.lin_order C.rel) :
  ∃ R : struct, isomorphic R A ∧ ∃ S : struct, isomorphic S B ∧ R.fld ∩ S.fld = ∅
  ∧ ∃ T : struct, isomorphic T C ∧ R.fld ∩ T.fld = ∅ ∧ S.fld ∩ T.fld = ∅ :=
⟨_, fst_fun_iso, _, fst_fun_iso, disj zero_ne_one, _, fst_fun_iso, disj zero_ne_two, disj one_ne_two⟩

lemma exists_lin_mem_order_type {ρ : Set} (ρot : ρ.order_type) : ∃ R : struct, R.fld.lin_order R.rel ∧ struct_to_set R ∈ ρ :=
begin
  obtain ⟨S, Sρ⟩ := order_type_inhab ρot,
  obtain ⟨R, SR, -, Rlin⟩ := of_mem_order_type ρot Sρ, subst SR,
  exact ⟨_, Rlin, Sρ⟩,
end

noncomputable def ot_repr (ρ : Set) : struct :=
if ρot : ρ.order_type then classical.some (exists_lin_mem_order_type ρot) else ⟨∅, ∅, empty_subset⟩
lemma ot_repr_lin {ρ : Set} (ρot : ρ.order_type) : ρ.ot_repr.fld.lin_order ρ.ot_repr.rel :=
begin
  obtain ⟨lin, -⟩ := classical.some_spec (exists_lin_mem_order_type ρot),
  rw [ot_repr, dif_pos ρot], exact lin,
end
lemma ot_repr_mem {ρ : Set} (ρot : ρ.order_type) : struct_to_set ρ.ot_repr ∈ ρ :=
begin
  obtain ⟨-, mem⟩ := classical.some_spec (exists_lin_mem_order_type ρot),
  rw [ot_repr, dif_pos ρot], exact mem,
end
lemma ot_repr_pioneering {ρ : Set} (ρot : ρ.order_type) : pioneering ρ.ot_repr :=
begin
  have hρ := ot_repr_mem ρot,
  rcases ρot with ⟨R, Rlin, ρR⟩, subst ρR,
  rw struct_mem_it at hρ, exact hρ.left,
end

lemma iso_repr_it {R : struct} (Rlin : R.fld.lin_order R.rel) : isomorphic R (it R).ot_repr :=
begin
  have mem := ot_repr_mem ⟨_, Rlin, rfl⟩,
  rw struct_mem_it at mem, exact mem.right,
end

lemma order_type_ext' {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type)
  (h : ∀ {T : struct}, struct_to_set T ∈ ρ ↔ struct_to_set T ∈ σ) : ρ = σ :=
order_type_ext ρot (ot_repr_mem ρot) σot (ot_repr_mem σot) @h

lemma order_type_eq_iff_repr_iso {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type) :
  ρ = σ ↔ isomorphic ρ.ot_repr σ.ot_repr :=
begin
  split,
    intro ρot, subst ρot, exact iso_refl,
  intro ρσ, apply order_type_ext ρot (ot_repr_mem ρot) σot (ot_repr_mem σot), intro T,
  rw [struct_mem_order_type ρot (ot_repr_mem ρot), struct_mem_order_type σot (ot_repr_mem σot)], split,
    rintro ⟨rank, iso, lin⟩, rw ←rank,
    exact ⟨rank_eq_of_iso_pioneering (iso_symm ρσ) (ot_repr_pioneering σot) (ot_repr_pioneering ρot),
      iso_trans (iso_symm ρσ) iso, lin_order_iso iso (ot_repr_lin ρot)⟩,
  rintro ⟨rank, iso, lin⟩, rw ←rank,
  exact ⟨rank_eq_of_iso_pioneering ρσ (ot_repr_pioneering ρot) (ot_repr_pioneering σot),
    iso_trans ρσ iso, lin_order_iso iso (ot_repr_lin σot)⟩,
end

lemma ot_eq_iff_exists_iso {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type) :
  ρ = σ ↔ ∃ R : struct, isomorphic R ρ.ot_repr ∧ ∃ S : struct, isomorphic S σ.ot_repr ∧ isomorphic R S :=
begin
  rw order_type_eq_iff_repr_iso ρot σot, split,
    intro iso, exact ⟨_, iso_refl, _, iso_refl, iso⟩,
  rintro ⟨R, Riso, S, Siso, iso⟩, exact iso_trans (iso_symm Riso) (iso_trans iso Siso),
end

noncomputable def ot_disj_repr (ρ σ : Set.{u}) : struct.{u} × struct.{u} :=
if ρot : ρ.order_type then
  (if σot : σ.order_type then
    classical.some (ex_disj_of_ord_type' (ot_repr_lin ρot) (ot_repr_lin σot))
  else ⟨⟨∅, ∅, empty_subset⟩, ⟨∅, ∅, empty_subset⟩⟩)
else ⟨⟨∅, ∅, empty_subset⟩, ⟨∅, ∅, empty_subset⟩⟩
lemma ot_disj_repr_left_iso {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type) :
  isomorphic (ρ.ot_disj_repr σ).fst ρ.ot_repr :=
begin
  obtain ⟨liso, riso, disj⟩ := classical.some_spec (ex_disj_of_ord_type' (ot_repr_lin ρot) (ot_repr_lin σot)),
  rw [ot_disj_repr, dif_pos ρot, dif_pos σot], exact liso,
end
lemma ot_disj_repr_right_iso {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type) :
  isomorphic (ρ.ot_disj_repr σ).snd σ.ot_repr :=
begin
  obtain ⟨liso, riso, disj⟩ := classical.some_spec (ex_disj_of_ord_type' (ot_repr_lin ρot) (ot_repr_lin σot)),
  rw [ot_disj_repr, dif_pos ρot, dif_pos σot], exact riso,
end
lemma ot_disj_repr_disj {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type) :
  (ρ.ot_disj_repr σ).fst.fld ∩ (ρ.ot_disj_repr σ).snd.fld = ∅ :=
begin
  obtain ⟨liso, riso, disj⟩ := classical.some_spec (ex_disj_of_ord_type' (ot_repr_lin ρot) (ot_repr_lin σot)),
  rw [ot_disj_repr, dif_pos ρot, dif_pos σot], exact disj,
end
lemma ot_disj_repr_left_lin {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type) :
  (ρ.ot_disj_repr σ).fst.fld.lin_order (ρ.ot_disj_repr σ).fst.rel :=
lin_order_iso (iso_symm (ot_disj_repr_left_iso ρot σot)) (ot_repr_lin ρot)
lemma ot_disj_repr_right_lin {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type) :
  (ρ.ot_disj_repr σ).snd.fld.lin_order (ρ.ot_disj_repr σ).snd.rel :=
lin_order_iso (iso_symm (ot_disj_repr_right_iso ρot σot)) (ot_repr_lin σot)

def add_rel (R S : struct) : Set := R.rel ∪ S.rel ∪ (R.fld.prod S.fld)
def add_struct (R S : struct.{u}) : struct.{u} :=
let h := union_subset_of_subset_of_subset (union_subset_of_subset_of_subset (subset_trans R.is_rel (prod_subset_of_subset_of_subset subset_union_left subset_union_left))
  (subset_trans S.is_rel (prod_subset_of_subset_of_subset subset_union_right subset_union_right)))
  (prod_subset_of_subset_of_subset subset_union_left subset_union_right) in
⟨R.fld ∪ S.fld, add_rel R S, h⟩

-- Lemma 8G (a)
lemma add_struct_lin {R : struct} (Rlin : R.fld.lin_order R.rel) {S : struct} (Slin : S.fld.lin_order S.rel)
  (disj : R.fld ∩ S.fld = ∅) : (add_struct R S).fld.lin_order (add_struct R S).rel :=
begin
  split,
  { exact (add_struct R S).is_rel, },
  { intros x y z, rw add_struct, dsimp, rw add_rel,
    simp only [mem_union, pair_mem_prod],
    rintros ((xyR|xyS)|⟨xR, yS⟩) ((yzR|yzS)|⟨yR, zS⟩),
    { left, left, exact Rlin.trans xyR yzR, },
    { replace xyR := Rlin.rel xyR, replace yzS := Slin.rel yzS,
      rw pair_mem_prod at xyR yzS, exfalso, apply mem_empty y,
      rw [←disj, mem_inter], exact ⟨xyR.right, yzS.left⟩, },
    { replace xyR := Rlin.rel xyR,
      rw pair_mem_prod at xyR, right, exact ⟨xyR.left, zS⟩, },
    { replace xyS := Slin.rel xyS, replace yzR := Rlin.rel yzR,
      rw pair_mem_prod at xyS yzR, exfalso, apply mem_empty y,
      rw [←disj, mem_inter], exact ⟨yzR.left, xyS.right⟩, },
    { left, right, exact Slin.trans xyS yzS, },
    { replace xyS := Slin.rel xyS,
      rw pair_mem_prod at xyS, exfalso, apply mem_empty y,
      rw [←disj, mem_inter], exact ⟨yR, xyS.right⟩, },
    { replace yzR := Rlin.rel yzR,
      rw pair_mem_prod at yzR, exfalso, apply mem_empty y,
      rw [←disj, mem_inter], exact ⟨yzR.left, yS⟩, },
    { replace yzS := Slin.rel yzS,
      rw pair_mem_prod at yzS, right, exact ⟨xR, yzS.right⟩, },
    { right, exact ⟨xR, zS⟩, }, },
  { rw add_struct, dsimp, rw add_rel, intro x, simp only [mem_union, pair_mem_prod],
    rintros ((xxR|xxS)|⟨xR, xS⟩),
    { exact Rlin.irrefl xxR, },
    { exact Slin.irrefl xxS, },
    { apply mem_empty x, rw [←disj, mem_inter], exact ⟨xR, xS⟩, }, },
  { rw add_struct, dsimp, intros x y, simp only [add_rel, mem_union, pair_mem_prod],
    rintros (xR|xS) (yR|yS) xny,
    { cases Rlin.conn xR yR xny,
        left, left, left, exact h,
      right, left, left, exact h, },
    { left, right, exact ⟨xR, yS⟩, },
    { right, right, exact ⟨yR, xS⟩, },
    { cases Slin.conn xS yS xny,
        left, left, right, exact h,
      right, left, right, exact h, }, },
end

noncomputable def ot_add (ρ σ : Set.{u}) : Set.{u} := it (add_struct (ρ.ot_disj_repr σ).fst (ρ.ot_disj_repr σ).snd)
lemma ot_add_ot {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type) : (ρ.ot_add σ).order_type :=
begin
  use add_struct (ρ.ot_disj_repr σ).fst (ρ.ot_disj_repr σ).snd,
  exact ⟨add_struct_lin (ot_disj_repr_left_lin ρot σot) (ot_disj_repr_right_lin ρot σot) (ot_disj_repr_disj ρot σot), rfl⟩,
end
lemma iso_add_of_iso {R S : struct} (RS : isomorphic R S) {T U : struct} (TU : isomorphic T U)
  (RT : R.fld ∩ T.fld = ∅) (SU : S.fld ∩ U.fld = ∅) : isomorphic (add_struct R T) (add_struct S U) :=
begin
  rcases RS with ⟨f, ⟨fonto, foto⟩, fiso⟩, rcases TU with ⟨g, ⟨gonto, goto⟩, giso⟩,
  refine ⟨f ∪ g, ⟨_, union_one_to_one foto goto _⟩, _⟩,
  { dsimp [add_struct],
    simp only [←fonto.right.left, ←fonto.right.right, ←gonto.right.left, ←gonto.right.right] at RT ⊢,
    exact union_fun fonto.left gonto.left RT, },
  { rw [fonto.right.right, gonto.right.right], exact SU },
  dsimp [add_struct, add_rel], simp only [mem_union, pair_mem_prod],
  rintros x y (xR|xT) (yR|yT),
  { rw [union_fun_value_left fonto gonto RT xR, union_fun_value_left fonto gonto RT yR],
    specialize fiso xR yR, rw [fiso, or_assoc, or_assoc], apply or_congr_right, split,
      rintro (xyT|⟨xR,yT⟩); exfalso,
      { apply mem_empty x, rw [←RT, mem_inter], refine ⟨xR, _⟩,
        suffices xyT' : x.pair y ∈ T.fld.prod T.fld,
          rw pair_mem_prod at xyT', exact xyT'.left,
        exact T.is_rel xyT, }, 
      { apply mem_empty y, rw [←RT, mem_inter], exact ⟨yR, yT⟩, },
    rintro (xyU|⟨xS,yU⟩); exfalso,
    { apply mem_empty (f.fun_value x), rw [←SU, mem_inter, ←fonto.right.right], rw ←fonto.right.left at xR,
      refine ⟨fun_value_def'' fonto.left xR, _⟩,
      suffices xyU' : (f.fun_value x).pair (f.fun_value y) ∈ U.fld.prod U.fld,
        rw pair_mem_prod at xyU', exact xyU'.left,
      exact U.is_rel xyU, },
    { apply mem_empty (f.fun_value y), rw [←SU, mem_inter, ←fonto.right.right], rw ←fonto.right.left at yR,
      refine ⟨fun_value_def'' fonto.left yR, yU⟩, }, },
  { rw [union_fun_value_left fonto gonto RT xR, union_fun_value_right fonto gonto RT yT],
    simp only [←fonto.right.right, ←gonto.right.right, ←fonto.right.left, ←gonto.right.left] at xR yT ⊢, split,
      intro h, right, exact ⟨fun_value_def'' fonto.left xR, fun_value_def'' gonto.left yT⟩,
    intro h, right, exact ⟨xR, yT⟩, },
  { rw [union_fun_value_right fonto gonto RT xT, union_fun_value_left fonto gonto RT yR], split,
      rintro ((xyR|xyT)|⟨xR,yT⟩); exfalso,
      { apply mem_empty x, rw [←RT, mem_inter], refine ⟨_, xT⟩,
        suffices xyR' : x.pair y ∈ R.fld.prod R.fld,
          rw pair_mem_prod at xyR', exact xyR'.left,
        exact R.is_rel xyR, },
      { apply mem_empty y, rw [←RT, mem_inter], refine ⟨yR, _⟩,
        suffices xyT' : x.pair y ∈ T.fld.prod T.fld,
          rw pair_mem_prod at xyT', exact xyT'.right,
        exact T.is_rel xyT, },
      { apply mem_empty x, rw [←RT, mem_inter], exact ⟨xR, xT⟩, },
    rintro ((xyS|xyU)|⟨xS,yU⟩); exfalso,
    { apply mem_empty (g.fun_value x), rw [←SU, mem_inter, ←gonto.right.right], rw ←gonto.right.left at xT,
      refine ⟨_, fun_value_def'' gonto.left xT⟩,
      suffices xyS : (g.fun_value x).pair (f.fun_value y) ∈ S.fld.prod S.fld,
        rw pair_mem_prod at xyS, exact xyS.left,
      exact S.is_rel xyS, },
    { apply mem_empty (f.fun_value y), rw [←SU, mem_inter, ←fonto.right.right], rw ←fonto.right.left at yR,
      refine ⟨fun_value_def'' fonto.left yR, _⟩,
      suffices xyS : (g.fun_value x).pair (f.fun_value y) ∈ U.fld.prod U.fld,
        rw pair_mem_prod at xyS, exact xyS.right,
      exact U.is_rel xyU, },
    { apply mem_empty (g.fun_value x), rw [←SU, mem_inter, ←gonto.right.right], rw ←gonto.right.left at xT,
      exact ⟨xS, fun_value_def'' gonto.left xT⟩, }, },
  { rw [union_fun_value_right fonto gonto RT xT, union_fun_value_right fonto gonto RT yT],
    specialize giso xT yT, rw giso, nth_rewrite 0 or_comm, nth_rewrite 2 or_comm,
    rw [←or_assoc, ←or_assoc], apply or_congr_left, split,
      rintros (⟨xR,yT⟩|xyR); exfalso; apply mem_empty x; rw [←RT, mem_inter],
      { exact ⟨xR, xT⟩, },
      { refine ⟨_, xT⟩,
        suffices xyR' : x.pair y ∈ R.fld.prod R.fld,
          rw pair_mem_prod at xyR', exact xyR'.left,
        exact R.is_rel xyR, },
    rintros (⟨xS,yU⟩|xyS); exfalso; apply mem_empty (g.fun_value x); rw [←SU, mem_inter, ←gonto.right.right];
    rw ←gonto.right.left at xT,
    { refine ⟨xS, fun_value_def'' gonto.left xT⟩, },
    { refine ⟨_, fun_value_def'' gonto.left xT⟩,
      suffices xyS' : (g.fun_value x).pair (g.fun_value y) ∈ S.fld.prod S.fld,
        rw pair_mem_prod at xyS', exact xyS'.left,
      exact S.is_rel xyS, }, },
end

lemma mem_ot_add {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type)
  {T : struct} : struct_to_set T ∈ ρ.ot_add σ ↔ pioneering T ∧ ∃ R : struct, isomorphic R ρ.ot_repr ∧ ∃ S : struct, isomorphic S σ.ot_repr ∧
  R.fld ∩ S.fld = ∅ ∧ isomorphic (add_struct R S) T :=
begin
  rw [ot_add, struct_mem_it], apply and_congr_right', split,
    intro iso,
    exact ⟨_, ot_disj_repr_left_iso ρot σot, _, ot_disj_repr_right_iso ρot σot, ot_disj_repr_disj ρot σot, iso⟩,
  rintro ⟨R, Riso, S, Siso, disj, iso⟩, refine iso_trans _ iso,
  apply iso_add_of_iso,
        exact (iso_trans (ot_disj_repr_left_iso ρot σot) (iso_symm Riso)),
      exact (iso_trans (ot_disj_repr_right_iso ρot σot) (iso_symm Siso)),
    exact ot_disj_repr_disj ρot σot,
  exact disj,
end

lemma iso_ot_add_repr {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type)
  {T : struct} : isomorphic T (ρ.ot_add σ).ot_repr ↔
  ∃ R : struct, isomorphic R ρ.ot_repr ∧ ∃ S : struct, isomorphic S σ.ot_repr ∧ R.fld ∩ S.fld = ∅ ∧ isomorphic (add_struct R S) T :=
begin
  have h := ot_repr_mem (ot_add_ot ρot σot),
  rw mem_ot_add ρot σot at h, rcases h with ⟨-, R, Riso, S, Siso, disj, iso⟩, split,
    intro iso', exact ⟨_, Riso, _, Siso, disj, iso_trans iso (iso_symm iso')⟩,
  rintro ⟨R', Riso', S', Siso', disj', iso'⟩,
  refine iso_trans (iso_symm iso') (iso_trans (iso_add_of_iso (iso_trans Riso' (iso_symm Riso)) (iso_trans Siso' (iso_symm Siso)) disj' disj) iso),
end

noncomputable def ord_ot (α : Set) : Set := it (eps_order_struct α)
lemma ord_ot_is_ot {α : Set} (αord : α.is_ordinal) : α.ord_ot.order_type :=
⟨_, (ordinal_well_ordered' αord).lin, rfl⟩
lemma ord_eq_of_ord_ot_eq {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal)
  (h : α.ord_ot = β.ord_ot) : α = β :=
begin
  rw [←eps_img_ord_eq_self αord, ←eps_img_ord_eq_self βord,
    ←iso_iff_eps_img_eq (ordinal_well_ordered' αord) (ordinal_well_ordered' βord), ←iso_type_eq_iff_iso],
  exact h,
end
lemma repr_ord_ot_iso {α : Set} (αord : α.is_ordinal) : isomorphic α.ord_ot.ot_repr α.eps_order_struct :=
iso_symm (struct_mem_it.mp (ot_repr_mem (ord_ot_is_ot αord))).right

def rev_struct (R : struct) : struct := ⟨R.fld, R.rel.inv, inv_sub_prod R.is_rel⟩
noncomputable def ot_rev (ρ : Set) : Set := it (rev_struct ρ.ot_repr)
lemma ot_rev_ot {ρ : Set} (ρot : ρ.order_type) : ρ.ot_rev.order_type :=
begin
  refine ⟨_, _, rfl⟩, rw rev_struct, dsimp, split,
  { exact (rev_struct _).is_rel, },
  { intros x y z xy yz, rw pair_mem_inv at xy yz ⊢, exact (ot_repr_lin ρot).trans yz xy,  },
  { intros x xx, rw pair_mem_inv at xx, exact (ot_repr_lin ρot).irrefl xx, },
  { intros x y hx hy xy, simp only [pair_mem_inv, or.comm], exact (ot_repr_lin ρot).conn hx hy xy, },
end
lemma it_rev_eq_of_iso {R S : struct} (RS : isomorphic R S) : it (rev_struct R) = it (rev_struct S) :=
begin
  rw iso_type_eq_iff_iso, rcases RS with ⟨f, ⟨fonto, foto⟩, corr⟩, refine ⟨f, ⟨fonto, foto⟩, _⟩,
  dsimp [rev_struct], simp only [pair_mem_inv], intros x y xR yR, exact corr yR xR,
end

lemma fin_ord_rev_ot_eq_self {n : Set} (nω : n ∈ ω) : n.ord_ot.ot_rev = n.ord_ot :=
begin
  have not := ord_ot_is_ot (nat_is_ord nω),
  have rot := ot_rev_ot not,
  rw [ot_rev, it_rev_eq_of_iso (repr_ord_ot_iso (nat_is_ord nω)), ord_ot, iso_type_eq_iff_iso],
  refine finite_lin_order_iso _ _ (ordinal_well_ordered (nat_is_ord nω)).lin,
    rw eps_order_struct_fld, exact nat_finite nω,
  rw [eps_order_struct_fld, eps_order_struct_rel],
  exact inv_lin_order (ordinal_well_ordered (nat_is_ord nω)).lin,
end

def mul_rel (R S : struct) : Set :=
pair_sep (λ x y, x.snd.pair y.snd ∈ S.rel ∨ x.snd = y.snd ∧ x.fst.pair y.fst ∈ R.rel) (R.fld.prod S.fld) (R.fld.prod S.fld)
def mul_struct (R S : struct) : struct := ⟨R.fld.prod S.fld, mul_rel R S, pair_sep_sub_prod⟩
noncomputable def ot_mul (ρ σ : Set) : Set := it (mul_struct ρ.ot_repr σ.ot_repr)

-- Lemma 8H (a)
lemma mul_struct_lin {R : struct} (Rlin : R.fld.lin_order R.rel) {S : struct} (Slin : S.fld.lin_order S.rel) :
  (mul_struct R S).fld.lin_order (mul_struct R S).rel :=
begin
  split,
  { exact (mul_struct R S).is_rel, },
  { intros a b c, rw mul_struct, dsimp, rw mul_rel, intros ab bc, rw pair_mem_pair_sep at ab bc,
    rw pair_mem_pair_sep' ab.left bc.right.left, rw [mem_prod, mem_prod] at ab bc,
    rcases ab with ⟨⟨x₁, hx₁, y₁, hy₁, ha⟩, ⟨x₂, hx₂, y₂, hy₂, hb⟩, c₁⟩,
    rcases bc with ⟨-, ⟨x₃, hx₃, y₃, hy₃, hc⟩, c₂⟩, subst ha, subst hb, subst hc,
    simp only [fst_congr, snd_congr] at c₁ c₂ ⊢,
    rcases c₁ with (yy₁|⟨yy₁, xx₁⟩); rcases c₂ with (yy₂|⟨yy₂, xx₂⟩),
          left, exact Slin.trans yy₁ yy₂,
        subst yy₂, left, exact yy₁,
      subst yy₁, left, exact yy₂,
    subst yy₁, subst yy₂, right, exact ⟨rfl, Rlin.trans xx₁ xx₂⟩, },
  { intro x, rw mul_struct, dsimp, rw [mul_rel, pair_mem_pair_sep, mem_prod],
    rintro ⟨-, -, (aaR|⟨-, bbS⟩)⟩,
      exact Slin.irrefl aaR,
    exact Rlin.irrefl bbS, },
  { rw mul_struct, dsimp, intros x y hx hy xny,
    rw [mul_rel, pair_mem_pair_sep' hx hy, pair_mem_pair_sep' hy hx], rw mem_prod at hx hy,
    rcases hx with ⟨a₁, ha₁, b₁, hb₁, xab⟩, rcases hy with ⟨a₂, ha₂, b₂, hb₂, yab⟩, subst xab, subst yab,
    simp only [fst_congr, snd_congr],
    by_cases beb : b₁ = b₂,
      by_cases aea : a₁ = a₂,
        subst aea, subst beb, exfalso, exact xny rfl,
      subst beb, cases Rlin.conn ha₁ ha₂ aea with ala ala,
        left, right, exact ⟨rfl, ala⟩,
      right, right, exact ⟨rfl, ala⟩,
    cases Slin.conn hb₁ hb₂ beb with blb blb,
      left, left, exact blb,
    right, left, exact blb, },
end
-- Lemma 8H (b)
lemma iso_mul_of_iso {R S : struct} (RS : isomorphic R S) {T U : struct} (TU : isomorphic T U)
  : isomorphic (mul_struct R T) (mul_struct S U) :=
begin
  rcases RS with ⟨f, fc, fiso⟩, rcases TU with ⟨g, gc, giso⟩,
  obtain ⟨honto, hoto⟩ := T6H_b_lemma fc gc,
  refine ⟨_, ⟨honto, hoto⟩, _⟩, dsimp [mul_struct], intros x y xRT yRT,
  rw ←honto.right.left at xRT yRT, rw [pair_sep_eq_fun_value xRT, pair_sep_eq_fun_value yRT], dsimp [mul_rel],
  rw honto.right.left at xRT yRT, rw [pair_mem_pair_sep' xRT yRT],
  rw mem_prod at xRT yRT, rcases xRT with ⟨r, rR, t, tT, xrt⟩, rcases yRT with ⟨r', rR', t', tT', yrt⟩,
  subst xrt, subst yrt, simp only [fst_congr, snd_congr],
  have fgrt : (f.fun_value r).pair (g.fun_value t) ∈ S.fld.prod U.fld,
    rw pair_mem_prod, rw ←fc.onto.right.left at rR, rw ←gc.onto.right.left at tT,
    rw [←fc.onto.right.right, ←gc.onto.right.right],
    exact ⟨fun_value_def'' fc.onto.left rR, fun_value_def'' gc.onto.left tT⟩,
  have fgrt' : (f.fun_value r').pair (g.fun_value t') ∈ S.fld.prod U.fld,
    rw pair_mem_prod, rw ←fc.onto.right.left at rR', rw ←gc.onto.right.left at tT',
    rw [←fc.onto.right.right, ←gc.onto.right.right],
    exact ⟨fun_value_def'' fc.onto.left rR', fun_value_def'' gc.onto.left tT'⟩,
  rw pair_mem_pair_sep' fgrt fgrt', simp only [fst_congr, snd_congr, giso tT tT', fiso rR rR'],
  rw eq_iff_fun_value_eq_of_oto gc.onto.left gc.oto _ _,
    rw gc.onto.right.left, exact tT,
  rw gc.onto.right.left, exact tT',
end

lemma ot_mul_ot {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type) : (ρ.ot_mul σ).order_type :=
begin
  use mul_struct ρ.ot_repr σ.ot_repr, exact ⟨mul_struct_lin (ot_repr_lin ρot) (ot_repr_lin σot), rfl⟩,
end

lemma mem_ot_mul {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type)
  {T : struct} : struct_to_set T ∈ ρ.ot_mul σ ↔ pioneering T ∧
  ∃ R S : struct, isomorphic R ρ.ot_repr ∧ isomorphic S σ.ot_repr ∧ isomorphic (mul_struct R S) T :=
begin
  rw [ot_mul, struct_mem_it], apply and_congr_right', split,
    intro iso,
    exact ⟨_, _, iso_refl, iso_refl, iso⟩,
  rintro ⟨R, S, Riso, Siso, iso⟩,
  exact iso_trans (iso_symm (iso_mul_of_iso Riso Siso)) iso,
end

lemma iso_ot_mul_repr {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type)
  {T : struct} : isomorphic T (ρ.ot_mul σ).ot_repr ↔
  ∃ R S : struct, isomorphic R ρ.ot_repr ∧ isomorphic S σ.ot_repr ∧ isomorphic (mul_struct R S) T :=
begin
  have h := ot_repr_mem (ot_mul_ot ρot σot),
  rw mem_ot_mul ρot σot at h, rcases h with ⟨-, R, S, Riso, Siso, iso⟩, split,
    intro iso', exact ⟨_, _, Riso, Siso, iso_trans iso (iso_symm iso')⟩,
  rintro ⟨R', S', Riso', Siso', iso'⟩,
  exact iso_trans (iso_symm iso') (iso_trans (iso_mul_of_iso (iso_trans Riso' (iso_symm Riso)) (iso_trans Siso' (iso_symm Siso))) iso),
end

lemma it_mul {R : struct} (Rlin : R.fld.lin_order R.rel) {S : struct} (Slin : S.fld.lin_order S.rel) :
  (it R).ot_mul (it S) = it (mul_struct R S) :=
begin
  rw [ot_mul, iso_type_eq_iff_iso],
  exact iso_mul_of_iso (iso_symm (iso_repr_it Rlin)) (iso_symm (iso_repr_it Slin)),
end

-- Theorem 8I (a)
theorem ot_add_assoc {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type) {τ : Set} (τot : τ.order_type) :
  (ρ.ot_add σ).ot_add τ = ρ.ot_add (σ.ot_add τ) :=
begin
  have ρσot := ot_add_ot ρot σot, have στot := ot_add_ot σot τot,
  obtain ⟨R, Riso, S, Siso, RSdisj, T, Tiso, RTdisj, STdisj⟩ := ex_3_disj (ot_repr_lin ρot) (ot_repr_lin σot) (ot_repr_lin τot),
  rw ot_eq_iff_exists_iso (ot_add_ot ρσot τot) (ot_add_ot ρot στot),
  refine ⟨add_struct (add_struct R S) T, _, add_struct R (add_struct S T), _, iso_of_eq _⟩,
      simp only [iso_ot_add_repr ρσot τot, iso_ot_add_repr ρot σot],
      refine ⟨_, ⟨_, Riso, _, Siso, RSdisj, iso_refl⟩, _, Tiso, _, iso_refl⟩,
      dsimp [add_struct], rw [union_inter, RTdisj, STdisj, union_empty],
    simp only [iso_ot_add_repr ρot στot, iso_ot_add_repr σot τot],
    refine ⟨_, Riso, _, ⟨_, Siso, _, Tiso, STdisj, iso_refl⟩, _, iso_refl⟩,
    dsimp [add_struct], rw [inter_union, RSdisj, RTdisj, union_empty],
  ext; dsimp [add_struct],
    rw union_assoc,
  dsimp [add_rel], rw [union_prod, prod_union], apply ext, finish,
end

lemma mul_assoc_lemma {R S T : struct} :
  isomorphic (mul_struct R (mul_struct S T)) (mul_struct (mul_struct R S) T) :=
begin
  use pair_sep_eq (R.fld.prod (S.fld.prod T.fld)) ((R.fld.prod S.fld).prod T.fld) (λ x, (x.fst.pair x.snd.fst).pair x.snd.snd),
  have deq : ((R.fld.prod (S.fld.prod T.fld)).pair_sep_eq ((R.fld.prod S.fld).prod T.fld)
      (λ x, (x.fst.pair x.snd.fst).pair x.snd.snd)).dom = R.fld.prod (S.fld.prod T.fld),
    apply pair_sep_eq_dom_eq,
    intros rst rstRST, simp only [mem_prod, exists_prop] at rstRST, dsimp,
    rcases rstRST with ⟨r, rR, st, ⟨s, sS, t, tT, rsrs⟩, rstrst⟩, subst rsrs, subst rstrst,
    simp only [fst_congr, snd_congr, pair_mem_prod], exact ⟨⟨rR, sS⟩, tT⟩, 
  refine ⟨⟨⟨pair_sep_eq_is_fun, deq, pair_sep_eq_ran_eq _⟩, pair_sep_eq_oto _⟩, _⟩,
  { intros rst rstRST, simp only [mem_prod, exists_prop] at rstRST,
    rcases rstRST with ⟨rs, ⟨r, rR, s, sS, rsrs⟩, t, tT, rstrst⟩, subst rsrs, subst rstrst,
    use r.pair (s.pair t), dsimp, simp only [fst_congr, snd_congr, pair_mem_prod],
    exact ⟨⟨rR, sS, tT⟩, rfl⟩, },
  { intros rst rstRST rst' rstRST' eq, dsimp at eq,
    simp only [mem_prod, exists_prop] at rstRST rstRST',
    rcases rstRST with ⟨r, rR, st, ⟨s, sS, t, tT, stst⟩, rstrst⟩, subst stst, subst rstrst,
    rcases rstRST' with ⟨r', rR', st', ⟨s', sS', t', tT', stst'⟩, rstrst'⟩, subst stst', subst rstrst',
    simp only [fst_congr, snd_congr] at eq,
    obtain ⟨rsrs, tt⟩ := pair_inj eq, obtain ⟨rr, ss⟩ := pair_inj rsrs,
    subst rr, subst ss, subst tt, },
  { dsimp [mul_struct, mul_rel], intros rst rst' rstRST rstRST',
    have rstD : rst ∈ ((R.fld.prod (S.fld.prod T.fld)).pair_sep_eq ((R.fld.prod S.fld).prod T.fld)
        (λ x, (x.fst.pair x.snd.fst).pair x.snd.snd)).dom,
      rw deq, exact rstRST,
    have rstD' : rst' ∈ ((R.fld.prod (S.fld.prod T.fld)).pair_sep_eq ((R.fld.prod S.fld).prod T.fld)
        (λ x, (x.fst.pair x.snd.fst).pair x.snd.snd)).dom,
      rw deq, exact rstRST',
    rw [pair_sep_eq_fun_value rstD, pair_sep_eq_fun_value rstD'], dsimp,
    rw pair_mem_pair_sep' rstRST rstRST', rw mem_prod at rstRST rstRST',
    rcases rstRST with ⟨r, rR, st, stST, rstrst⟩, rcases rstRST' with ⟨r', rR', st', stST', rstrst'⟩,
    subst rstrst, subst rstrst', simp only [fst_congr, snd_congr, pair_mem_pair_sep' stST stST'],
    rw mem_prod at stST stST',
    rcases stST with ⟨s, sS, t, tT, stst⟩, rcases stST' with ⟨s', sS', t', tT', stst'⟩, subst stst, subst stst',
    simp only [fst_congr, snd_congr],
    have rsmem : r.pair s ∈ R.fld.prod S.fld, rw pair_mem_prod, exact ⟨rR, sS⟩,
    have rsmem' : r'.pair s' ∈ R.fld.prod S.fld, rw pair_mem_prod, exact ⟨rR', sS'⟩,
    have rstmem : (r.pair s).pair t ∈ (R.fld.prod S.fld).prod T.fld,
      rw pair_mem_prod, exact ⟨rsmem, tT⟩,
    have rstmem' : (r'.pair s').pair t' ∈ (R.fld.prod S.fld).prod T.fld,
      rw pair_mem_prod, exact ⟨rsmem', tT'⟩,
    rw deq at rstD rstD',
    simp only [fst_congr, snd_congr, pair_mem_pair_sep' rstmem rstmem', pair_mem_pair_sep' rsmem rsmem'],
    clear deq rsmem rsmem' rstmem rstmem' rstD' rstD, split,
      rintro ((tt|⟨tt,ss⟩)|⟨stst,rr⟩),
          exact or.inl tt,
        subst tt, exact or.inr ⟨rfl, or.inl ss⟩,
      obtain ⟨ss, tt⟩ := pair_inj stst, subst ss, subst tt,
      exact or.inr ⟨rfl, or.inr ⟨rfl, rr⟩⟩,
    rintros (tt|⟨tt,(ss|⟨ss,rr⟩)⟩),
        exact or.inl (or.inl tt),
      subst tt, exact or.inl (or.inr ⟨rfl, ss⟩),
    subst tt, subst ss, exact or.inr ⟨rfl, rr⟩, },
end

-- Theorem 8I (a)
theorem ot_mul_assoc {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type) {τ : Set} (τot : τ.order_type) :
  (ρ.ot_mul σ).ot_mul τ = ρ.ot_mul (σ.ot_mul τ) :=
begin
  have ρσot := ot_mul_ot ρot σot, have στot := ot_mul_ot σot τot,
  apply order_type_ext' (ot_mul_ot ρσot τot) (ot_mul_ot ρot στot),
  simp only [mem_ot_mul ρσot τot, mem_ot_mul ρot στot], intro U, apply and_congr_right',
  simp only [iso_ot_mul_repr ρot σot, iso_ot_mul_repr σot τot], split,
    rintros ⟨RS, T, ⟨R, S, Riso, Siso, RSiso⟩, Tiso, RSTiso⟩,
    refine ⟨_, _, Riso, ⟨_, _, Siso, Tiso, iso_refl⟩, _⟩,
    refine iso_trans _ RSTiso, refine iso_trans mul_assoc_lemma (iso_mul_of_iso RSiso iso_refl),
  rintros ⟨R, ST, Riso, ⟨S, T, Siso, Tiso, STiso⟩, RSTiso⟩,
  refine ⟨_, _, ⟨_, _, Riso, Siso, iso_refl⟩, Tiso, _⟩,
  refine iso_trans _ RSTiso, apply iso_trans _ (iso_mul_of_iso iso_refl STiso),
  exact iso_symm mul_assoc_lemma,
end

lemma pair_sep_union_prod_eq {p : Set → Set → Prop} {A B C : Set}
  (BA : B ⊆ A) (CA : C ⊆ A) : (pair_sep p A A) ∪ (B.prod C) = pair_sep (λ x y, p x y ∨ x.pair y ∈ B.prod C) A A :=
begin
  apply @rel_ext' A A _ _ _ pair_sep_sub_prod _,
    exact union_subset_of_subset_of_subset pair_sep_sub_prod (prod_subset_of_subset_of_subset BA CA),
  intros x xA y yA, rw [mem_union, pair_mem_pair_sep' xA yA, pair_mem_pair_sep' xA yA],
end

lemma pair_sep_union_eq {p q : Set → Set → Prop} {A B : Set} :
  (pair_sep p A A) ∪ (pair_sep q B B) = pair_sep (λ x y, x ∈ A ∧ y ∈ A ∧ p x y ∨ x ∈ B ∧ y ∈ B ∧ q x y) (A ∪ B) (A ∪ B) :=
begin
  refine @rel_ext' (A ∪ B) (A ∪ B) _ _ _ pair_sep_sub_prod _,
    apply union_subset_of_subset_of_subset,
      exact subset_trans pair_sep_sub_prod (prod_subset_of_subset_of_subset subset_union_left subset_union_left),
    exact subset_trans pair_sep_sub_prod (prod_subset_of_subset_of_subset subset_union_right subset_union_right),
  intros x xAB y yAB, rw pair_mem_pair_sep' xAB yAB,
  simp only [mem_union] at *, simp only [pair_mem_pair_sep],
end

-- Theorem 8I (b)
theorem ot_add_mul {ρ : Set} (ρot : ρ.order_type) {σ : Set} (σot : σ.order_type) {τ : Set} (τot : τ.order_type) :
  ρ.ot_mul (σ.ot_add τ) = (ρ.ot_mul σ).ot_add (ρ.ot_mul τ) :=
begin
  have στot := ot_add_ot σot τot, have ρσot := ot_mul_ot ρot σot, have ρτot := ot_mul_ot ρot τot,
  let R := ρ.ot_repr,
  have Riso : isomorphic R ρ.ot_repr := iso_refl,
  obtain ⟨⟨S, T⟩, Siso, Tiso, STdisj⟩ := ex_disj_of_ord_type' (ot_repr_lin σot) (ot_repr_lin τot),
  dsimp at STdisj Siso Tiso,
  have disj' : R.fld.prod S.fld ∩ R.fld.prod T.fld = ∅, rw [←prod_inter, STdisj, prod_empty_eq_empty],
  rw ot_eq_iff_exists_iso (ot_mul_ot ρot στot) (ot_add_ot ρσot ρτot),
  refine ⟨mul_struct R (add_struct S T), _, add_struct (mul_struct R S) (mul_struct R T), _, iso_of_eq _⟩,
      simp only [iso_ot_mul_repr ρot στot, iso_ot_add_repr σot τot],
      refine ⟨_, _, Riso, ⟨_, Siso, _, Tiso, STdisj, iso_refl⟩, iso_refl⟩,
    simp only [iso_ot_add_repr ρσot ρτot, iso_ot_mul_repr ρot σot, iso_ot_mul_repr ρot τot],
    refine ⟨_, ⟨_, _, Riso, Siso, iso_refl⟩, _, ⟨_, _, Riso, Tiso, iso_refl⟩, disj', iso_refl⟩,
  have e : R.fld.prod (S.fld ∪ T.fld) = R.fld.prod S.fld ∪ R.fld.prod T.fld,
    rw prod_union,
  ext,
    dsimp [mul_struct, add_struct], exact e,
  let U := R.fld.prod (S.fld ∪ T.fld),
  apply @rel_ext' U U,
      dsimp [mul_struct, add_struct, mul_rel, add_rel], exact pair_sep_sub_prod,
    dsimp [U, add_struct, add_rel, mul_struct], rw e, apply union_subset_of_subset_of_subset,
      dsimp [mul_rel], apply union_subset_of_subset_of_subset,
        exact subset_trans pair_sep_sub_prod (prod_subset_of_subset_of_subset subset_union_left subset_union_left),
      exact subset_trans pair_sep_sub_prod (prod_subset_of_subset_of_subset subset_union_right subset_union_right),
    exact prod_subset_of_subset_of_subset subset_union_left subset_union_right,
  simp only [U, mem_prod], rintros x ⟨r, rR, st, stST, xrst⟩ y ⟨r', rR', st', stST', yrst⟩; subst xrst; subst yrst,
  simp only [mul_struct, add_struct, mul_rel, add_rel],
  rw [pair_sep_union_eq, pair_sep_union_prod_eq subset_union_left subset_union_right],
  have rstRST : r.pair st ∈ R.fld.prod (S.fld ∪ T.fld),
    rw pair_mem_prod, exact ⟨rR, stST⟩,
  have rstRST' : r'.pair st' ∈ R.fld.prod (S.fld ∪ T.fld),
    rw pair_mem_prod, exact ⟨rR', stST'⟩,
  simp only [←e, pair_mem_pair_sep' rstRST rstRST', fst_congr, snd_congr, mem_union, pair_mem_prod], split,
    rintro (((stst|stst)|⟨stS,stT⟩)|⟨stst,rr⟩),
    { have stst' := S.is_rel stst, rw pair_mem_prod at stst',
      left, left, exact ⟨⟨rR, stst'.left⟩, ⟨rR', stst'.right⟩, or.inl stst⟩, },
    { have stst' := T.is_rel stst, rw pair_mem_prod at stst',
      left, right, exact ⟨⟨rR, stst'.left⟩, ⟨rR', stst'.right⟩, or.inl stst⟩, },
    { right, exact ⟨⟨rR, stS⟩, ⟨rR', stT⟩⟩, },
    { subst stst, rw mem_union at stST, rcases stST with (stS|stT),
        left, left, exact ⟨⟨rR, stS⟩, ⟨rR', stS⟩, or.inr ⟨rfl, rr⟩⟩,
      left, right, exact ⟨⟨rR, stT⟩, ⟨rR', stT⟩, or.inr ⟨rfl, rr⟩⟩, },
  finish,
end

-- Theorem 8I (c)
theorem ot_add_zero {ρ : Set} (ρot : ρ.order_type) : ρ.ot_add (ord_ot ∅) = ρ :=
begin
  obtain ⟨⟨R, E⟩, Riso, Eiso, REdisj⟩ :=
    ex_disj_of_ord_type' (ot_repr_lin ρot) (ot_repr_lin (ord_ot_is_ot zero_is_ord)),
  dsimp at Riso Eiso REdisj,
  rw ot_eq_iff_exists_iso (ot_add_ot ρot (ord_ot_is_ot zero_is_ord)) ρot,
  refine ⟨add_struct R E, _, R, Riso, _⟩,
    rw iso_ot_add_repr ρot (ord_ot_is_ot zero_is_ord),
    refine ⟨_, Riso, _, Eiso, REdisj, iso_refl⟩,
  refine iso_trans (iso_add_of_iso iso_refl (iso_trans Eiso (repr_ord_ot_iso zero_is_ord)) REdisj _) _,
    rw [eps_order_struct_fld, inter_empty],
  apply iso_of_eq, ext; dsimp [add_struct],
    rw union_empty,
  rw [add_rel, eps_order_struct_fld, eps_order_struct_rel, prod_empty_eq_empty, union_empty],
  suffices h : eps_order ∅ = ∅,
    rw [h, union_empty],
  rw [eps_order, rel_eq_empty pair_sep_is_rel],
  intros x y xy, rw pair_mem_pair_sep at xy, exact mem_empty _ xy.left,
end

-- Theorem 8I (c)
theorem ot_zero_add {ρ : Set} (ρot : ρ.order_type) : (ord_ot ∅).ot_add ρ = ρ :=
begin
  obtain ⟨⟨E, R⟩, Eiso, Riso, REdisj⟩ :=
    ex_disj_of_ord_type' (ot_repr_lin (ord_ot_is_ot zero_is_ord)) (ot_repr_lin ρot),
  dsimp at Riso Eiso REdisj,
  rw ot_eq_iff_exists_iso (ot_add_ot (ord_ot_is_ot zero_is_ord) ρot) ρot,
  refine ⟨add_struct E R, _, R, Riso, _⟩,
    rw iso_ot_add_repr (ord_ot_is_ot zero_is_ord) ρot,
    refine ⟨_, Eiso, _, Riso, REdisj, iso_refl⟩,
  refine iso_trans (iso_add_of_iso (iso_trans Eiso (repr_ord_ot_iso zero_is_ord)) iso_refl REdisj _) _,
    rw [eps_order_struct_fld, inter_comm, inter_empty],
  apply iso_of_eq, ext; dsimp [add_struct],
    rw [union_comm, union_empty],
  rw [add_rel, eps_order_struct_fld, eps_order_struct_rel, empty_prod_eq_empty, union_empty],
  suffices h : eps_order ∅ = ∅,
    rw [h, union_comm, union_empty],
  rw [eps_order, rel_eq_empty pair_sep_is_rel],
  intros x y xy, rw pair_mem_pair_sep at xy, exact mem_empty _ xy.left,
end

-- Theorem 8I (c)
theorem ot_mul_one {ρ : Set} (ρot : ρ.order_type) : ρ.ot_mul (ord_ot one) = ρ :=
begin
  have one_ord := nat_is_ord one_nat,
  let R := ρ.ot_repr,
  have Riso : isomorphic R ρ.ot_repr := iso_refl,
  let S := one.eps_order_struct,
  have Siso : isomorphic S one.ord_ot.ot_repr := iso_symm (repr_ord_ot_iso one_ord),
  rw ot_eq_iff_exists_iso (ot_mul_ot ρot (ord_ot_is_ot one_ord)) ρot,
  refine ⟨mul_struct R S, _, R, Riso, _⟩,
    rw iso_ot_mul_repr ρot (ord_ot_is_ot one_ord),
    refine ⟨_, _, Riso, Siso, iso_refl⟩,
  let f := pair_sep_eq (R.fld.prod S.fld) R.fld fst,
  have fd : f.dom = R.fld.prod S.fld, apply pair_sep_eq_dom_eq,
    simp only [S, eps_order_struct_fld, one, succ, union_empty, mem_prod, exists_prop, mem_singleton],
    rintros x ⟨r, rR, s, sS, xrs⟩, subst xrs, rw fst_congr, exact rR,
  refine ⟨f, ⟨⟨pair_sep_eq_is_fun, fd, pair_sep_eq_ran_eq _⟩, pair_sep_eq_oto _⟩, _⟩;
  simp only [S, eps_order_struct_fld, one, succ, union_empty, mem_prod, exists_prop, mem_singleton],
  { intros r rR, refine ⟨_, ⟨_, rR, _, rfl, rfl⟩, _⟩, rw fst_congr, },
  { rintros x ⟨r, rR, s, sS, xrs⟩ y ⟨r', rR', s', sS', yrs⟩ rr, subst xrs, subst yrs,
    simp only [fst_congr] at rr, subst rr, subst sS, subst sS', },
  { simp only [mul_struct, eps_order_struct_fld, mul_rel, eps_order_struct_rel],
    intros x y xRS yRS, rw pair_mem_pair_sep' xRS yRS,
    have xf : x ∈ f.dom, simp only [fd, S, eps_order_struct_fld, one, succ, union_empty], exact xRS,
    have yf : y ∈ f.dom, simp only [fd, S, eps_order_struct_fld, one, succ, union_empty], exact yRS,
    rw [pair_sep_eq_fun_value xf, pair_sep_eq_fun_value yf],
    simp only [mem_prod, exists_prop] at xRS yRS,
    rcases xRS with ⟨r, rR, s, sS, xrs⟩, rcases yRS with ⟨r', rR', s', sS', yrs⟩, subst xrs, subst yrs,
    simp only [fst_congr, snd_congr],
    rw pair_mem_eps_order' sS sS', rw mem_singleton at sS sS', subst sS, subst sS',
    finish, },
end

-- Theorem 8I (c)
theorem ot_one_mul {ρ : Set} (ρot : ρ.order_type) : (ord_ot one).ot_mul ρ = ρ :=
begin
  have one_ord := nat_is_ord one_nat,
  let R := ρ.ot_repr,
  have Riso : isomorphic R ρ.ot_repr := iso_refl,
  let S := one.eps_order_struct,
  have Siso : isomorphic S one.ord_ot.ot_repr := iso_symm (repr_ord_ot_iso one_ord),
  rw ot_eq_iff_exists_iso (ot_mul_ot (ord_ot_is_ot one_ord) ρot) ρot,
  refine ⟨mul_struct S R, _, R, Riso, _⟩,
    rw iso_ot_mul_repr (ord_ot_is_ot one_ord) ρot,
    refine ⟨_, _, Siso, Riso, iso_refl⟩,
  let f := pair_sep_eq (S.fld.prod R.fld) R.fld snd,
  have fd : f.dom = S.fld.prod R.fld, apply pair_sep_eq_dom_eq,
    simp only [S, eps_order_struct_fld, one, succ, union_empty, mem_prod, exists_prop, mem_singleton],
    rintros x ⟨r, rR, s, sS, xrs⟩, subst xrs, rw snd_congr, exact sS,
  refine ⟨f, ⟨⟨pair_sep_eq_is_fun, fd, pair_sep_eq_ran_eq _⟩, pair_sep_eq_oto _⟩, _⟩;
  simp only [S, eps_order_struct_fld, one, succ, union_empty, mem_prod, exists_prop, mem_singleton],
  { intros r rR, refine ⟨_, ⟨_, rfl, _, rR, rfl⟩, _⟩, rw snd_congr, },
  { rintros x ⟨r, rR, s, sS, xrs⟩ y ⟨r', rR', s', sS', yrs⟩ rr, subst xrs, subst yrs,
    simp only [snd_congr] at rr, subst rr, subst rR, subst rR', },
  { simp only [mul_struct, eps_order_struct_fld, mul_rel, eps_order_struct_rel],
    intros x y xRS yRS, rw pair_mem_pair_sep' xRS yRS,
    have xf : x ∈ f.dom, simp only [fd, S, eps_order_struct_fld, one, succ, union_empty], exact xRS,
    have yf : y ∈ f.dom, simp only [fd, S, eps_order_struct_fld, one, succ, union_empty], exact yRS,
    rw [pair_sep_eq_fun_value xf, pair_sep_eq_fun_value yf],
    simp only [mem_prod, exists_prop] at xRS yRS,
    rcases xRS with ⟨r, rR, s, sS, xrs⟩, rcases yRS with ⟨r', rR', s', sS', yrs⟩, subst xrs, subst yrs,
    simp only [fst_congr, snd_congr],
    rw pair_mem_eps_order' rR rR', rw mem_singleton at rR rR', subst rR, subst rR',
    finish, },
end

-- Theorem 8I (c)
theorem ot_mul_zero {ρ : Set} (ρot : ρ.order_type) : ρ.ot_mul (ord_ot ∅) = ord_ot ∅ :=
begin
  let R := ρ.ot_repr,
  have Riso : isomorphic R ρ.ot_repr := iso_refl,
  let S := eps_order_struct ∅,
  have Siso : isomorphic S (ord_ot ∅).ot_repr := iso_symm (repr_ord_ot_iso zero_is_ord),
  rw ot_eq_iff_exists_iso (ot_mul_ot ρot (ord_ot_is_ot zero_is_ord)) (ord_ot_is_ot zero_is_ord),
  refine ⟨mul_struct R S, _, _, Siso, iso_of_eq _⟩,
    rw iso_ot_mul_repr ρot (ord_ot_is_ot zero_is_ord),
    exact ⟨_, _, Riso, Siso, iso_refl⟩,
  ext; simp only [mul_struct, mul_rel, eps_order, S, eps_order_struct_fld, prod_empty_eq_empty, eps_order_struct_rel],
  apply rel_ext pair_sep_is_rel pair_sep_is_rel,
  intros x y, simp only [pair_mem_pair_sep], split,
    rintros ⟨xe, _, _⟩, exfalso, exact mem_empty _ xe,
  rintros ⟨xe, _, _⟩, exfalso, exact mem_empty _ xe,
end

-- Theorem 8I (c)
theorem ot_zero_mul {ρ : Set} (ρot : ρ.order_type) : (ord_ot ∅).ot_mul ρ = ord_ot ∅ :=
begin
  let R := ρ.ot_repr,
  have Riso : isomorphic R ρ.ot_repr := iso_refl,
  let S := eps_order_struct ∅,
  have Siso : isomorphic S (ord_ot ∅).ot_repr := iso_symm (repr_ord_ot_iso zero_is_ord),
  rw ot_eq_iff_exists_iso (ot_mul_ot (ord_ot_is_ot zero_is_ord) ρot) (ord_ot_is_ot zero_is_ord),
  refine ⟨mul_struct S R, _, _, Siso, iso_of_eq _⟩,
    rw iso_ot_mul_repr (ord_ot_is_ot zero_is_ord) ρot,
    exact ⟨_, _, Siso, Riso, iso_refl⟩,
  ext; simp only [mul_struct, mul_rel, eps_order, S, eps_order_struct_fld, empty_prod_eq_empty, eps_order_struct_rel],
  apply rel_ext pair_sep_is_rel pair_sep_is_rel,
  intros x y, simp only [pair_mem_pair_sep], split,
    rintros ⟨xe, _, _⟩, exfalso, exact mem_empty _ xe,
  rintros ⟨xe, _, _⟩, exfalso, exact mem_empty _ xe,
end

lemma prod_corr_of_corr {A B f : Set} (AB : A.correspondence B f)
  {C D g : Set} (CD : C.correspondence D g) :
  (A.prod C).correspondence (B.prod D) (pair_sep_eq (A.prod C) (B.prod D) (λ z, (f.fun_value z.fst).pair (g.fun_value z.snd))) :=
begin
  refine ⟨⟨pair_sep_eq_is_fun, pair_sep_eq_dom_eq _, pair_sep_eq_ran_eq _⟩, pair_sep_eq_oto _⟩,
  { dsimp, simp only [pair_mem_prod, ←AB.onto.right.right, ←CD.onto.right.right],
    intro x, rw mem_prod, rintro ⟨a, aA, c, cC, xac⟩, subst xac, rw [fst_congr, snd_congr],
    refine ⟨fun_value_def'' AB.onto.left _, fun_value_def'' CD.onto.left _⟩,
      rwa AB.onto.right.left,
    rwa CD.onto.right.left, },
  { dsimp, simp only [mem_prod, exists_prop,
      ←AB.onto.right.right, mem_ran_iff AB.onto.left, AB.onto.right.left,
      ←CD.onto.right.right, mem_ran_iff CD.onto.left, CD.onto.right.left],
    rintros y ⟨b, ⟨a, aA, ab⟩, d, ⟨c, cC, dc⟩, ybd⟩, subst ybd, subst ab, subst dc,
    use a.pair c, rw [fst_congr, snd_congr], exact ⟨⟨_, aA, _, cC, rfl⟩, rfl⟩, },
  { dsimp, simp only [mem_prod, exists_prop],
    rintros x₁ ⟨a₁, aA₁, c₁, cC₁, xac₁⟩ x₂ ⟨a₂, aA₂, c₂, cC₂, xac₂⟩ acac, subst xac₁, subst xac₂,
    simp only [fst_congr, snd_congr] at acac,
    obtain ⟨faa, fcc⟩ := pair_inj acac,
    rw ←AB.onto.right.left at aA₁ aA₂, rw ←CD.onto.right.left at cC₁ cC₂,
    rw [from_one_to_one AB.onto.left AB.oto aA₁ aA₂ faa,
      from_one_to_one CD.onto.left CD.oto cC₁ cC₂ fcc], },
end

-- exercise 12
lemma it_add_eq_lex {R : struct} (Rlin : R.fld.lin_order R.rel)
  {S : struct} (Slin : S.fld.lin_order S.rel) :
  let C := R.fld.prod {∅} ∪ S.fld.prod {one} in
  (it R).ot_add (it S) = it ⟨C, pair_sep (λ x y, x.snd ∈ y.snd ∨ x.snd = y.snd ∧ (x.snd = ∅ ∧ x.fst.pair y.fst ∈ R.rel ∨ x.snd = one ∧ x.fst.pair y.fst ∈ S.rel)) C C, pair_sep_sub_prod⟩ :=
begin
  dsimp,
  set C := R.fld.prod {∅} ∪ S.fld.prod {one},
  set T : struct := ⟨C, pair_sep (λ x y, x.snd ∈ y.snd ∨ x.snd = y.snd ∧ (x.snd = ∅ ∧ x.fst.pair y.fst ∈ R.rel ∨ x.snd = one ∧ x.fst.pair y.fst ∈ S.rel)) C C, pair_sep_sub_prod⟩,
  have Tlin : T.fld.lin_order T.rel, refine ⟨T.is_rel, _, _, _⟩,
    { intros x y z xy yz, dsimp [T] at xy yz ⊢,
      rw pair_mem_pair_sep at xy yz, rcases xy with ⟨xC, yC, xy⟩, rcases yz with ⟨-, zC, yz⟩,
      rw pair_mem_pair_sep' xC zC,
      simp only [C, mem_union, mem_prod, exists_prop, mem_singleton] at xC yC zC,
      rcases xC with (⟨x₁, hx₁, x₂, hx₂, xxx⟩|⟨x₁, hx₁, x₂, hx₂, xxx⟩); subst xxx; subst hx₂;
      rcases yC with (⟨y₁, hy₁, y₂, hy₂, yyy⟩|⟨y₁, hy₁, y₂, hy₂, yyy⟩); subst yyy; subst hy₂;
      rcases xy with (xy₂|⟨xy₂, (⟨x₂, xy₁⟩|⟨x₂, xy₁⟩)⟩); simp only [fst_congr, snd_congr] at *,
      { exfalso, exact mem_empty _ xy₂, },
      rotate,
      { exfalso, exact zero_ne_one x₂, },
      rotate,
      { exfalso, exact zero_ne_one xy₂, },
      { exfalso, exact zero_ne_one xy₂, },
      { exfalso, exact mem_empty _ xy₂, },
      { exfalso, exact zero_ne_one xy₂.symm, },
      { exfalso, exact zero_ne_one xy₂.symm, },
      { exfalso, exact nat_not_mem_self one_nat xy₂, },
      { exfalso, exact zero_ne_one x₂.symm, },
      rotate,
      all_goals { rcases zC with (⟨z₁, hz₁, z₂, hz₂, zzz⟩|⟨z₁, hz₁, z₂, hz₂, zzz⟩); subst zzz; subst hz₂;
        rcases yz with (yz₂|⟨yz₂, (⟨y₂, yz₁⟩|⟨y₂, yz₁⟩)⟩); simp only [fst_congr, snd_congr] at *, },
      { exfalso, exact mem_empty _ yz₂, },
      { right, exact ⟨rfl, or.inl ⟨rfl, Rlin.trans xy₁ yz₁⟩⟩, },
      { exfalso, exact zero_ne_one y₂, },
      { left, rw [one, succ, union_empty, mem_singleton], },
      { exfalso, exact zero_ne_one yz₂, },
      { exfalso, exact zero_ne_one y₂, },
      { exfalso, exact mem_empty _ yz₂, },
      { exfalso, exact zero_ne_one y₂.symm, },
      { exfalso, exact zero_ne_one yz₂.symm, },
      { exfalso, exact nat_not_mem_self one_nat yz₂, },
      { exfalso, exact zero_ne_one y₂.symm, },
      { left, rw [one, succ, union_empty, mem_singleton], },
      { exfalso, exact mem_empty _ yz₂, },
      { exfalso, exact zero_ne_one y₂.symm, },
      { exfalso, exact zero_ne_one yz₂.symm, },
      { exfalso, exact nat_not_mem_self one_nat yz₂, },
      { exfalso, exact zero_ne_one y₂.symm, },
      { right, exact ⟨rfl, or.inr ⟨rfl, Slin.trans xy₁ yz₁⟩⟩, }, },
    { dsimp [T, C], intros x xx,
      simp only [pair_mem_pair_sep, mem_union, mem_prod, exists_prop, mem_singleton] at xx,
      rcases xx with ⟨(⟨x₁, hx₁, x₂, hx₂, xxx⟩|⟨x₁, hx₁, x₂, hx₂, xxx⟩), -, (xx₂|⟨xx₂, (⟨x₂, xx₁⟩|⟨x₂, xx₁⟩)⟩)⟩;
      subst xxx; subst hx₂; simp only [fst_congr, snd_congr] at *,
      { exfalso, exact mem_empty _ xx₂, },
      { exact Rlin.irrefl xx₁, },
      { exfalso, exact zero_ne_one x₂, },
      { exfalso, exact nat_not_mem_self one_nat xx₂, },
      { exfalso, exact zero_ne_one x₂.symm, },
      { exact Slin.irrefl xx₁, }, },
    { dsimp [T, C], intros x y xC yC xy,
      rw [pair_mem_pair_sep' xC yC, pair_mem_pair_sep' yC xC],
      simp only [mem_union, mem_prod, exists_prop, mem_singleton] at xC yC,
      rcases xC with (⟨x₁, hx₁, x₂, hx₂, xxx⟩|⟨x₁, hx₁, x₂, hx₂, xxx⟩); subst xxx; subst hx₂;
      rcases yC with (⟨y₁, hy₁, y₂, hy₂, yyy⟩|⟨y₁, hy₁, y₂, hy₂, yyy⟩); subst yyy; subst hy₂;
      simp only [fst_congr, snd_congr],
      { cases Rlin.conn hx₁ hy₁ (fst_ne_of_pair_ne xy) with xy yx,
          left, right, exact ⟨rfl, or.inl ⟨rfl, xy⟩⟩,
        right, right, exact ⟨rfl, or.inl ⟨rfl, yx⟩⟩, },
      { left, left, rw [one, succ, union_empty, mem_singleton], },
      { right, left, rw [one, succ, union_empty, mem_singleton], },
      { cases Slin.conn hx₁ hy₁ (fst_ne_of_pair_ne xy) with xy yx,
          left, right, exact ⟨rfl, or.inr ⟨rfl, xy⟩⟩,
        right, right, exact ⟨rfl, or.inr ⟨rfl, yx⟩⟩, }, },
  simp only [ot_eq_iff_exists_iso (ot_add_ot ⟨_, Rlin, rfl⟩ ⟨_, Slin, rfl⟩) ⟨_, Tlin, rfl⟩,
    iso_ot_add_repr ⟨_, Rlin, rfl⟩ ⟨_, Slin, rfl⟩],
  let R' : struct := ⟨R.fld.prod {∅}, fun_order (R.fld.prod {∅}) R.rel (pair_sep_eq (R.fld.prod {∅}) R.fld fst), pair_sep_sub_prod⟩,
  let S' : struct := ⟨S.fld.prod {one}, fun_order (S.fld.prod {one}) S.rel (pair_sep_eq (S.fld.prod {one}) S.fld fst), pair_sep_sub_prod⟩,
  refine ⟨_, ⟨_, fst_fun_iso, _, fst_fun_iso, disj zero_ne_one, @iso_add_of_iso _ R' _ _ S' _ _ (disj zero_ne_one)⟩, _, iso_repr_it Tlin, _⟩,
    { obtain ⟨f, fcorr, fiso⟩ := iso_symm (iso_repr_it Rlin),
      let F := pair_sep_eq (f.dom.prod {∅}) (f.ran.prod {∅}) (λ z, (f.fun_value z.fst).pair ((id {∅}).fun_value z.snd)),
      have Fcorr := prod_corr_of_corr fcorr id_corr,
      refine ⟨F, _, _⟩; dsimp [F, R']; simp only [fcorr.onto.right.left, fcorr.onto.right.right],
        exact Fcorr,
      intros x y xD yD, rw ←Fcorr.onto.right.left at xD yD,
      rw [pair_sep_eq_fun_value xD, pair_sep_eq_fun_value yD], dsimp,
      rw Fcorr.onto.right.left at xD yD, rw [fun_order, pair_mem_pair_sep' xD yD],
      simp only [mem_prod, exists_prop, mem_singleton] at xD yD,
      rcases xD with ⟨a, ha, b, hb, xab⟩, rcases yD with ⟨a', ha', b', hb', yab⟩,
      subst xab, subst yab, subst hb, subst hb', simp only [fst_congr, snd_congr, id_singleton_value],
      have fa : f.fun_value a ∈ R.fld, rw ←fcorr.onto.right.right, apply fun_value_def'' fcorr.onto.left,
        rw fcorr.onto.right.left, exact ha,
      have fa' : f.fun_value a' ∈ R.fld, rw ←fcorr.onto.right.right, apply fun_value_def'' fcorr.onto.left,
        rw fcorr.onto.right.left, exact ha',
      have h₁ : (f.fun_value a).pair ∅ ∈ R.fld.prod {∅},
        rw [pair_mem_prod, mem_singleton], exact ⟨fa, rfl⟩,
      have h₂ : (f.fun_value a').pair ∅ ∈ R.fld.prod {∅},
        rw [pair_mem_prod, mem_singleton], exact ⟨fa', rfl⟩,
      rw [fun_order, pair_mem_pair_sep' h₁ h₂, fst_fun_value fa, fst_fun_value fa', fst_fun_value ha, fst_fun_value ha'],
      exact fiso ha ha', },
    { obtain ⟨f, fcorr, fiso⟩ := iso_symm (iso_repr_it Slin),
      let F := pair_sep_eq (f.dom.prod {one}) (f.ran.prod {one}) (λ z, (f.fun_value z.fst).pair ((id {one}).fun_value z.snd)),
      have Fcorr := prod_corr_of_corr fcorr id_corr,
      refine ⟨F, _, _⟩; dsimp [F, S']; simp only [fcorr.onto.right.left, fcorr.onto.right.right],
        exact Fcorr,
      intros x y xD yD, rw ←Fcorr.onto.right.left at xD yD,
      rw [pair_sep_eq_fun_value xD, pair_sep_eq_fun_value yD], dsimp,
      rw Fcorr.onto.right.left at xD yD, rw [fun_order, pair_mem_pair_sep' xD yD],
      simp only [mem_prod, exists_prop, mem_singleton] at xD yD,
      rcases xD with ⟨a, ha, b, hb, xab⟩, rcases yD with ⟨a', ha', b', hb', yab⟩,
      subst xab, subst yab, subst hb, subst hb', simp only [fst_congr, snd_congr, id_singleton_value],
      have fa : f.fun_value a ∈ S.fld, rw ←fcorr.onto.right.right, apply fun_value_def'' fcorr.onto.left,
        rw fcorr.onto.right.left, exact ha,
      have fa' : f.fun_value a' ∈ S.fld, rw ←fcorr.onto.right.right, apply fun_value_def'' fcorr.onto.left,
        rw fcorr.onto.right.left, exact ha',
      have h₁ : (f.fun_value a).pair one ∈ S.fld.prod {one},
        rw [pair_mem_prod, mem_singleton], exact ⟨fa, rfl⟩,
      have h₂ : (f.fun_value a').pair one ∈ S.fld.prod {one},
        rw [pair_mem_prod, mem_singleton], exact ⟨fa', rfl⟩,
      rw [fun_order, pair_mem_pair_sep' h₁ h₂, fst_fun_value fa, fst_fun_value fa', fst_fun_value ha, fst_fun_value ha'],
      exact fiso ha ha', },
    { dsimp, exact disj zero_ne_one, },
  dsimp [R', S', T, C], apply iso_of_eq, ext,
    dsimp [add_struct], refl,
  dsimp [add_struct, add_rel], refine rel_ext' _ pair_sep_sub_prod _,
    refine union_subset_of_subset_of_subset (union_subset_of_subset_of_subset _ _) (prod_subset_of_subset_of_subset subset_union_left subset_union_right),
    { exact subset_trans pair_sep_sub_prod (prod_subset_of_subset_of_subset subset_union_left subset_union_left), },
    { exact subset_trans pair_sep_sub_prod (prod_subset_of_subset_of_subset subset_union_right subset_union_right), },
  simp only [fun_order], intros x xC y yC,
  simp only [pair_mem_pair_sep' xC yC, pair_sep_union_eq, pair_sep_union_prod_eq subset_union_left subset_union_right],
  have dR : ((R.fld.prod {∅}).pair_sep_eq R.fld fst).dom = R.fld.prod {∅},
    apply pair_sep_eq_dom_eq, simp only [mem_prod, exists_prop, mem_singleton],
    rintros z ⟨w, hw, b, -, zwb⟩, subst zwb, rw fst_congr, exact hw,
  have dS : ((S.fld.prod {one}).pair_sep_eq S.fld fst).dom = S.fld.prod {one},
    apply pair_sep_eq_dom_eq, simp only [mem_prod, exists_prop, mem_singleton],
    rintros z ⟨w, hw, b, -, zwb⟩, subst zwb, rw fst_congr, exact hw,
  split,
    rintros ((⟨xR', yR', xy⟩|⟨xS', yS', xy⟩)|xy),
    { have xf : x ∈ ((R.fld.prod {∅}).pair_sep_eq R.fld fst).dom,
        rw dR, exact xR',
      have yf : y ∈ ((R.fld.prod {∅}).pair_sep_eq R.fld fst).dom,
        rw dR, exact yR',
      simp only [mem_prod, exists_prop, mem_singleton] at xR' yR',
      rcases xR' with ⟨z, zR, t, ht, xzt⟩, rcases yR' with ⟨z', zR', t', ht', yzt⟩,
      subst xzt, subst yzt, subst ht, subst ht',
      simp only [pair_sep_eq_fun_value xf, pair_sep_eq_fun_value yf, fst_congr, snd_congr] at *,
      right, exact ⟨rfl, or.inl ⟨rfl, xy⟩⟩, },
    { have xf : x ∈ ((S.fld.prod {one}).pair_sep_eq S.fld fst).dom,
        rw dS, exact xS',
      have yf : y ∈ ((S.fld.prod {one}).pair_sep_eq S.fld fst).dom,
        rw dS, exact yS',
      simp only [mem_prod, exists_prop, mem_singleton] at xS' yS',
      rcases xS' with ⟨z, zS, t, ht, xzt⟩, rcases yS' with ⟨z', zS', t', ht', yzt⟩,
      subst xzt, subst yzt, subst ht, subst ht',
      simp only [pair_sep_eq_fun_value xf, pair_sep_eq_fun_value yf, fst_congr, snd_congr] at *,
      right, exact ⟨rfl, or.inr ⟨rfl, xy⟩⟩, },
    { simp only [pair_mem_prod, mem_prod, exists_prop, mem_singleton] at xy,
      rcases xy with ⟨x', ⟨z, -, t, ht, xzt'⟩, y', ⟨z', _, t', ht', yzt'⟩, xyxy⟩,
      obtain ⟨xx, yy⟩ := pair_inj xyxy,
      subst xx, subst yy, subst xzt', subst yzt', subst ht, subst ht',
      left, simp only [snd_congr], rw [one, succ, union_empty, mem_singleton], },
  rw mem_union at xC yC,
  rcases xC with (xR'|xS'); rcases yC with (yR'|yS'),
  { have xf : x ∈ ((R.fld.prod {∅}).pair_sep_eq R.fld fst).dom,
      rw dR, exact xR',
    have yf : y ∈ ((R.fld.prod {∅}).pair_sep_eq R.fld fst).dom,
      rw dR, exact yR',
    simp only [pair_sep_eq_fun_value xf, pair_sep_eq_fun_value yf, pair_mem_prod, mem_union],
    rintro (tt|⟨tt, (⟨tt', zz⟩|⟨tt', zz⟩)⟩),
        all_goals {
        simp only [mem_prod, exists_prop, mem_singleton] at xR' yR',
        rcases xR' with ⟨z, zR, t, ht, xzt⟩, rcases yR' with ⟨z', zR', t', ht', yzt⟩,
        subst xzt, subst yzt, subst ht, subst ht',
        simp only [fst_congr, snd_congr] at *, },
        exfalso, exact mem_empty _ tt,
      left, left, simp only [pair_mem_prod, mem_singleton],
      have zz' := R.is_rel zz, rw pair_mem_prod at zz',
      exact ⟨⟨zz'.left, rfl⟩, ⟨zz'.right, rfl⟩, zz⟩,
    exfalso, exact zero_ne_one tt', },
  { have xf : x ∈ ((R.fld.prod {∅}).pair_sep_eq R.fld fst).dom,
      rw dR, exact xR',
    have yf : y ∈ ((S.fld.prod {one}).pair_sep_eq S.fld fst).dom,
      rw dS, exact yS',
    simp only [pair_sep_eq_fun_value xf, pair_sep_eq_fun_value yf, pair_mem_prod, mem_union],
    rintro (tt|⟨tt, (⟨tt', zz⟩|⟨tt', zz⟩)⟩),
        all_goals {
        simp only [mem_prod, exists_prop, mem_singleton] at xR' yS',
        rcases xR' with ⟨z, zR, t, ht, xzt⟩, rcases yS' with ⟨z', zS', t', ht', yzt⟩,
        subst xzt, subst yzt, subst ht, subst ht',
        simp only [fst_congr, snd_congr] at *, },
        right, simp only [pair_mem_prod, mem_singleton], exact ⟨⟨zR, rfl⟩, zS', rfl⟩,
      exfalso, exact zero_ne_one tt,
    exfalso, exact zero_ne_one tt, },
  { have xf : x ∈ ((S.fld.prod {one}).pair_sep_eq S.fld fst).dom,
      rw dS, exact xS',
    have yf : y ∈ ((R.fld.prod {∅}).pair_sep_eq R.fld fst).dom,
      rw dR, exact yR',
    simp only [pair_sep_eq_fun_value xf, pair_sep_eq_fun_value yf, pair_mem_prod, mem_union],
    rintro (tt|⟨tt, (⟨tt', zz⟩|⟨tt', zz⟩)⟩),
        all_goals {
        simp only [mem_prod, exists_prop, mem_singleton] at xS' yR',
        rcases xS' with ⟨z, zS, t, ht, xzt⟩, rcases yR' with ⟨z', zR', t', ht', yzt⟩,
        subst xzt, subst yzt, subst ht, subst ht',
        simp only [fst_congr, snd_congr] at *, },
        exfalso, exact mem_empty _ tt,
      exfalso, exact zero_ne_one tt.symm,
    exfalso, exact zero_ne_one tt.symm, },
  { have xf : x ∈ ((S.fld.prod {one}).pair_sep_eq S.fld fst).dom,
      rw dS, exact xS',
    have yf : y ∈ ((S.fld.prod {one}).pair_sep_eq S.fld fst).dom,
      rw dS, exact yS',
    simp only [pair_sep_eq_fun_value xf, pair_sep_eq_fun_value yf, pair_mem_prod, mem_union],
    rintro (tt|⟨tt, (⟨tt', zz⟩|⟨tt', zz⟩)⟩),
        all_goals {
        simp only [mem_prod, exists_prop, mem_singleton] at xS' yS',
        rcases xS' with ⟨z, zS, t, ht, xzt⟩, rcases yS' with ⟨z', zS', t', ht', yzt⟩,
        subst xzt, subst yzt, subst ht, subst ht',
        simp only [fst_congr, snd_congr] at *, },
        exfalso, exact ord_mem_irrefl (nat_is_ord one_nat) tt,
      exfalso, exact zero_ne_one tt'.symm,
    left, right, simp only [pair_mem_prod, mem_singleton],
    have zz' := S.is_rel zz, rw pair_mem_prod at zz',
    exact ⟨⟨zz'.left, rfl⟩, ⟨zz'.right, rfl⟩, zz⟩, },
end

lemma add_struct_well_order {A : struct} (Awell : A.fld.well_order A.rel)
  {B : struct} (Bwell : B.fld.well_order B.rel) (AB : A.fld ∩ B.fld = ∅) :
  let R : struct := add_struct A B in R.fld.well_order R.rel :=
begin
  refine ⟨add_struct_lin Awell.lin Bwell.lin AB, _⟩,
  intros C CE CAB,
  by_cases CAE : C ∩ A.fld ≠ ∅,
    have CA : C ∩ A.fld ⊆ A.fld := inter_subset_right,
    obtain ⟨m, mCA, mle⟩ := Awell.well CAE CA,
    have mC : m ∈ C, rw mem_inter at mCA, exact mCA.left,
    refine ⟨m, mC, _⟩, rintro ⟨d, dC, dm⟩,
    have dCA : d ∈ C ∩ A.fld, rw mem_inter, refine ⟨dC, _⟩,
      have dAB : d ∈ A.fld ∨ d ∈ B.fld, rw ←mem_union, exact CAB dC,
      rcases dAB with (dA|dB),
        exact dA,
      simp only [add_struct, add_rel, mem_union, pair_mem_prod] at dm, rcases dm with ((dmA|dmB)|⟨dA, -⟩),
          replace dmA := A.is_rel dmA, rw pair_mem_prod at dmA,
          exact dmA.left,
        exfalso, apply mem_empty m, rw [←AB, mem_inter], rw mem_inter at mCA,
        replace dmB := B.is_rel dmB, rw pair_mem_prod at dmB,
        exact ⟨mCA.right, dmB.right⟩,
      exact dA,
    refine mle ⟨_, dCA, _⟩,
    simp only [add_struct, add_rel, mem_union, pair_mem_prod] at dm, rcases dm with ((dmA|dmB)|⟨-, mB⟩),
        exact dmA,
      exfalso, apply mem_empty m, rw [←AB, mem_inter], rw mem_inter at mCA,
      replace dmB := B.is_rel dmB, rw pair_mem_prod at dmB,
      exact ⟨mCA.right, dmB.right⟩,
    exfalso, apply mem_empty m, rw [←AB, mem_inter], rw mem_inter at mCA, exact ⟨mCA.right, mB⟩,
  push_neg at CAE,
  have CB : C ⊆ B.fld, intros x xC,
    have xAB : x ∈ A.fld ∨ x ∈ B.fld, rw ←mem_union, exact CAB xC,
    rcases xAB with (xA|xB),
      exfalso, apply mem_empty x, rw [←CAE, mem_inter], exact ⟨xC, xA⟩,
    exact xB,
  obtain ⟨m, mC, mle⟩ := Bwell.well CE CB,
  refine ⟨m, mC, _⟩, rintro ⟨d, dC, dm⟩, apply mle, refine ⟨d, dC, _⟩,
  simp only [add_struct, add_rel, mem_union, pair_mem_prod] at dm, rcases dm with ((dmA|dmB)|dmAB),
      exfalso, apply mem_empty d, rw [←CAE, mem_inter],
      replace dmA := A.is_rel dmA, rw pair_mem_prod at dmA,
      exact ⟨dC, dmA.left⟩,
    exact dmB,
  exfalso, apply mem_empty d, rw [←CAE, mem_inter], exact ⟨dC, dmAB.left⟩,
end

lemma lex_well_order {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  let C := α.prod {∅} ∪ β.prod {one} in
  let R : struct := ⟨C, pair_sep (λ x y, x.snd ∈ y.snd ∨ x.snd = y.snd ∧ (x.snd = ∅ ∧ x.fst.pair y.fst ∈ α.eps_order ∨ x.snd = one ∧ x.fst.pair y.fst ∈ β.eps_order)) C C, pair_sep_sub_prod⟩ in
  R.fld.well_order R.rel :=
begin
  let disj := (it α.eps_order_struct).ot_disj_repr (it β.eps_order_struct),
  apply @well_order_iso (add_struct disj.fst disj.snd),
    rw ←iso_type_eq_iff_iso, exact it_add_eq_lex (ordinal_well_ordered' αord).lin (ordinal_well_ordered' βord).lin,
  have αot : (it α.eps_order_struct).order_type := ⟨_, (ordinal_well_ordered' αord).lin, rfl⟩,
  have βot : (it β.eps_order_struct).order_type := ⟨_, (ordinal_well_ordered' βord).lin, rfl⟩,
  refine add_struct_well_order (well_order_iso _ (ordinal_well_ordered' αord)) (well_order_iso _ (ordinal_well_ordered' βord)) (ot_disj_repr_disj αot βot),
    refine iso_symm (iso_trans (ot_disj_repr_left_iso αot βot) (iso_symm (iso_repr_it (ordinal_well_ordered' αord).lin))),
  refine iso_symm (iso_trans (ot_disj_repr_right_iso αot βot) (iso_symm (iso_repr_it (ordinal_well_ordered' βord).lin))),
end

lemma pair_mem_lex {R S : struct} {x y : Set} (hxy : x.pair y ∈
  pair_sep
    (λ x y,
       x.snd ∈ y.snd ∨
         x.snd = y.snd ∧
           (x.snd = ∅ ∧ x.fst.pair y.fst ∈ R.rel ∨ x.snd = one ∧ x.fst.pair y.fst ∈ S.rel))
    (R.fld.prod {∅} ∪ S.fld.prod {one})
    (R.fld.prod {∅} ∪ S.fld.prod {one})) :
    (∃ a, a ∈ R.fld ∧ x = pair a ∅ ∧ ∃ b, b ∈ S.fld ∧ y = pair b one) ∨
    (∃ a, a ∈ R.fld ∧ x = pair a ∅ ∧ ∃ b, b ∈ R.fld ∧ y = pair b ∅ ∧ a.pair b ∈ R.rel) ∨
    (∃ a, a ∈ S.fld ∧ x = pair a one ∧ ∃ b, b ∈ S.fld ∧ y = pair b one ∧ a.pair b ∈ S.rel) :=
begin
  rw pair_mem_pair_sep at hxy, rcases hxy with ⟨xC, yC, xy⟩,
  simp only [C, mem_union, mem_prod, exists_prop, mem_singleton] at xC yC,
  rcases xC with (⟨x₁, hx₁, x₂, hx₂, xxx⟩|⟨x₁, hx₁, x₂, hx₂, xxx⟩); subst xxx; subst hx₂;
  rcases yC with (⟨y₁, hy₁, y₂, hy₂, yyy⟩|⟨y₁, hy₁, y₂, hy₂, yyy⟩); subst yyy; subst hy₂;
  rcases xy with (xy₂|⟨xy₂, (⟨x₂, xy₁⟩|⟨x₂, xy₁⟩)⟩); simp only [fst_congr, snd_congr] at *,
  { exfalso, exact mem_empty _ xy₂, },
  { right, left, exact ⟨_, hx₁, rfl, _, hy₁, rfl, xy₁⟩, },
  { exfalso, exact zero_ne_one x₂, },
  { left, exact ⟨_, hx₁, rfl, _, hy₁, rfl⟩, },
  { exfalso, exact zero_ne_one xy₂, },
  { exfalso, exact zero_ne_one xy₂, },
  { exfalso, exact mem_empty _ xy₂, },
  { exfalso, exact zero_ne_one xy₂.symm, },
  { exfalso, exact zero_ne_one xy₂.symm, },
  { exfalso, exact nat_not_mem_self one_nat xy₂, },
  { exfalso, exact zero_ne_one x₂.symm, },
  { right, right, exact ⟨_, hx₁, rfl, _, hy₁, rfl, xy₁⟩, },
end

def wo_type (ρ : Set) : Prop := ∃ R : struct, R.fld.well_order R.rel ∧ ρ = it R

lemma ot_of_wo_type {ρ : Set} (ρwot : ρ.wo_type) : ρ.order_type :=
exists.elim ρwot (λ R hR, ⟨_, hR.left.lin, hR.right⟩)

lemma wo_type_of_mem {ρ : Set} (ρot : ρ.order_type)
  {R : struct} (Rwell : R.fld.well_order R.rel) (Rρ : struct_to_set R ∈ ρ) :
  ρ.wo_type :=
begin
  rcases ρot with ⟨S, Slin, Sρ⟩, subst Sρ,
  refine ⟨R, Rwell, _⟩, rw struct_mem_it at Rρ,
  rw iso_type_eq_iff_iso, exact Rρ.right,
end

lemma wo_type_of_iso {ρ : Set} (ρot : ρ.order_type)
  {R : struct} (Rwell : R.fld.well_order R.rel) (Riso : isomorphic R ρ.ot_repr) :
  ρ.wo_type :=
wo_type_of_mem ρot (well_order_iso Riso Rwell) (ot_repr_mem ρot)

lemma well_order_of_mem_wo_type {ρ : Set} (ρwo : ρ.wo_type)
  {R : struct} (Rρ : struct_to_set R ∈ ρ) : R.fld.well_order R.rel :=
begin
  rcases ρwo with ⟨S, Swell, ρS⟩, subst ρS,
  rw struct_mem_it at Rρ, exact well_order_iso Rρ.right Swell,
end

lemma well_order_of_iso_wo_repr {ρ : Set} (ρwo : ρ.wo_type)
  {R : struct} (Riso : isomorphic R ρ.ot_repr) : R.fld.well_order R.rel :=
well_order_iso (iso_symm Riso) (well_order_of_mem_wo_type ρwo (ot_repr_mem (ot_of_wo_type ρwo)))

lemma repr_wo_type_well_order {ρ : Set} (ρwo : ρ.wo_type) :
  ρ.ot_repr.fld.well_order ρ.ot_repr.rel :=
well_order_of_mem_wo_type ρwo (ot_repr_mem (ot_of_wo_type ρwo))

theorem exists_unique_ord_eq_wo_type {ρ : Set} (ρwot : ρ.wo_type) : ∃! α : Set, α.is_ordinal ∧ α.ord_ot = ρ :=
begin
  obtain ⟨α, αord, αiso⟩ := exists_iso_ord (repr_wo_type_well_order ρwot),
  have he : α.ord_ot = ρ,
    rw ot_eq_iff_exists_iso (ord_ot_is_ot αord) (ot_of_wo_type ρwot),
    exact ⟨_, iso_symm (repr_ord_ot_iso αord), _, iso_refl, αiso⟩,
  refine ⟨_, ⟨αord, he⟩, _⟩,
  dsimp, rintros β ⟨βord, βρ⟩, rw ←he at βρ, exact ord_eq_of_ord_ot_eq βord αord βρ,
end

theorem ord_ot_wot {α : Set} (αord : α.is_ordinal) : α.ord_ot.wo_type :=
⟨_, ordinal_well_ordered' αord, rfl⟩

theorem ord_ot_ot {α : Set} (αord : α.is_ordinal) : α.ord_ot.order_type :=
ot_of_wo_type (ord_ot_wot αord)

lemma well_order_of_it_wot {R : struct} (wot : (it R).wo_type) : R.fld.well_order R.rel :=
begin
  rcases wot with ⟨S, Swell, RS⟩, refine well_order_iso _ Swell,
  rw ←iso_type_eq_iff_iso, exact RS.symm,
end

-- Theorem 8J
theorem wot_add_wot {ρ : Set} (ρwot : ρ.wo_type) {σ : Set} (σwot : σ.wo_type) : (ρ.ot_add σ).wo_type :=
begin
  have ρot := ot_of_wo_type ρwot, have σot := ot_of_wo_type σwot,
  let A := (ρ.ot_disj_repr σ).fst, let B := (ρ.ot_disj_repr σ).snd,
  have AB : A.fld ∩ B.fld = ∅ := ot_disj_repr_disj ρot σot,
  have Awell : A.fld.well_order A.rel := well_order_of_iso_wo_repr ρwot (ot_disj_repr_left_iso ρot σot),
  have Bwell : B.fld.well_order B.rel := well_order_of_iso_wo_repr σwot (ot_disj_repr_right_iso ρot σot),
  let R := add_struct A B,
  have Rwell : R.fld.well_order R.rel := add_struct_well_order Awell Bwell AB,
  apply wo_type_of_iso (ot_add_ot ρot σot) Rwell,
  rw iso_ot_add_repr ρot σot,
  exact ⟨_, ot_disj_repr_left_iso ρot σot, _, ot_disj_repr_right_iso ρot σot, AB, iso_refl⟩,
end

-- Theorem 8J
theorem wot_mul_wot {ρ : Set} (ρwot : ρ.wo_type) {σ : Set} (σwot : σ.wo_type) : (ρ.ot_mul σ).wo_type :=
begin
  have ρot := ot_of_wo_type ρwot, have σot := ot_of_wo_type σwot,
  let A := ρ.ot_repr, let B := σ.ot_repr,
  have Awell : A.fld.well_order A.rel := well_order_of_iso_wo_repr ρwot iso_refl,
  have Bwell : B.fld.well_order B.rel := well_order_of_iso_wo_repr σwot iso_refl,
  let R := mul_struct A B,
  have Rwell : R.fld.well_order R.rel,
    refine ⟨mul_struct_lin Awell.lin Bwell.lin, _⟩,
    intros C CE CAB,
    obtain ⟨b, bC, ble⟩ := Bwell.well (ran_ne_of_ne CAB CE) (ran_sub_of_sub_prod CAB),
    let D : Set := {a ∈ A.fld | a.pair b ∈ C},
    have DE : D ≠ ∅,
      apply ne_empty_of_inhabited,
      rw mem_ran at bC, rcases bC with ⟨a, abC⟩,
      obtain abAB := CAB abC, simp only [R, mul_struct, mem_prod] at abAB,
      rcases abAB with ⟨a', aA', b', bB', abab⟩,
      obtain ⟨aa, bb⟩ := pair_inj abab, subst aa, subst bb, use a,
      rw mem_sep, exact ⟨aA', abC⟩,
    obtain ⟨a, aD, ale⟩ := Awell.well DE sep_subset,
    have abC : a.pair b ∈ C,
      rw mem_sep at aD, exact aD.right,
    refine ⟨_, abC, _⟩, rintro ⟨d, dC, dab⟩,
    have dR : d ∈ R.fld := CAB dC,
    have abR : a.pair b ∈ R.fld := CAB abC,
    dsimp [R, mul_struct] at dR abR,
    simp only [R, mul_struct, mul_rel, pair_mem_pair_sep' dR abR] at dab,
    rw mem_prod at dR, rcases dR with ⟨x, xA, y, yB, dxy⟩, subst dxy,
    simp only [fst_congr, snd_congr] at dab, rcases dab with (yb|⟨ybx, xa⟩),
      apply ble, refine ⟨_, _, yb⟩, rw mem_ran, exact ⟨_, dC⟩,
    subst ybx, apply ale, use x, rw mem_sep, exact ⟨⟨xA, dC⟩, xa⟩,
  apply wo_type_of_iso (ot_mul_ot ρot σot) Rwell,
  rw iso_ot_mul_repr ρot σot,
  exact ⟨_, _, iso_refl, iso_refl, iso_refl⟩,
end

lemma mul_struct_well_order {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  let R : struct := mul_struct α.eps_order_struct β.eps_order_struct in
  R.fld.well_order R.rel :=
begin
  dsimp, refine @well_order_iso (mul_struct α.ord_ot.ot_repr β.ord_ot.ot_repr) _ _ _,
    apply iso_mul_of_iso (iso_symm (iso_repr_it (ordinal_well_ordered' αord).lin)) (iso_symm (iso_repr_it (ordinal_well_ordered' βord).lin)),
  apply well_order_of_it_wot,
  have h := wot_mul_wot (ord_ot_wot αord) (ord_ot_wot βord),
  rw ot_mul at h, exact h,
end

lemma exists_ord_eq_ot_add {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  ∃! γ : Set, γ.is_ordinal ∧ γ.ord_ot = α.ord_ot.ot_add β.ord_ot :=
exists_unique_ord_eq_wo_type (wot_add_wot (ord_ot_wot αord) (ord_ot_wot βord))

lemma exists_ord_eq_ot_mul {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  ∃! γ : Set, γ.is_ordinal ∧ γ.ord_ot = α.ord_ot.ot_mul β.ord_ot :=
exists_unique_ord_eq_wo_type (wot_mul_wot (ord_ot_wot αord) (ord_ot_wot βord))

noncomputable def ord_add (α β : Set) : Set :=
if αord : α.is_ordinal then
if βord : β.is_ordinal then
classical.some (exists_ord_eq_ot_add αord βord)
else ∅ else ∅

noncomputable def ord_mul (α β : Set) : Set :=
if αord : α.is_ordinal then
if βord : β.is_ordinal then
classical.some (exists_ord_eq_ot_mul αord βord)
else ∅ else ∅

lemma ord_add_ord {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  (α.ord_add β).is_ordinal :=
begin
  simp only [ord_add, dif_pos αord, dif_pos βord],
  exact (classical.some_spec (exists_ord_eq_ot_add αord βord)).left.left,
end

lemma ord_mul_ord {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  (α.ord_mul β).is_ordinal :=
begin
  simp only [ord_mul, dif_pos αord, dif_pos βord],
  exact (classical.some_spec (exists_ord_eq_ot_mul αord βord)).left.left,
end

lemma ot_add_eq_add_ot {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  (α.ord_add β).ord_ot = α.ord_ot.ot_add β.ord_ot :=
begin
  simp only [ord_add, dif_pos αord, dif_pos βord],
  exact (classical.some_spec (exists_ord_eq_ot_add αord βord)).left.right,
end

lemma ot_mul_eq_mul_ot {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  (α.ord_mul β).ord_ot = α.ord_ot.ot_mul β.ord_ot :=
begin
  simp only [ord_mul, dif_pos αord, dif_pos βord],
  exact (classical.some_spec (exists_ord_eq_ot_mul αord βord)).left.right,
end

def singleton_struct (x : Set) : struct := ⟨{x}, ∅, empty_subset⟩

lemma singleton_struct_lin {x : Set} :
let R := x.singleton_struct in R.fld.lin_order R.rel :=
begin
  dsimp, refine ⟨empty_subset, _, _, _⟩,
      intros a b c ab bc, exfalso, exact mem_empty _ ab,
    intros a aa, exfalso, exact mem_empty _ aa,
  intros a b ax bx ab, exfalso, simp only [singleton_struct, mem_singleton] at ax bx,
  subst ax, subst bx, exact ab rfl,
end

lemma singleton_struct_iso {x y : Set} : isomorphic x.singleton_struct y.singleton_struct :=
begin
  refine ⟨{x.pair y}, ⟨single_pair_onto, single_pair_oto⟩, _⟩,
  dsimp [singleton_struct], intros a b ha hb, exact iff_of_not_of_not (mem_empty _) (mem_empty _),
end

theorem ord_add_one_eq_succ {α : Set} (αord : α.is_ordinal) : α.ord_add one = α.succ :=
begin
  have αone := ord_add_ord αord one_is_ord, have αord' := succ_ord_of_ord αord,
  apply ord_eq_of_ord_ot_eq αone αord',
  rw [ot_eq_iff_exists_iso (ord_ot_ot αone) (ord_ot_ot αord'), ot_add_eq_add_ot αord one_is_ord],
  refine ⟨add_struct α.eps_order_struct α.singleton_struct, _, α.succ.eps_order_struct, iso_symm (repr_ord_ot_iso αord'), iso_of_eq _⟩,
    rw iso_ot_add_repr (ord_ot_ot αord) (ord_ot_ot one_is_ord),
    refine ⟨_, iso_symm (repr_ord_ot_iso αord), _, iso_trans (@singleton_struct_iso α ∅) (iso_trans (iso_of_eq _) (iso_symm (repr_ord_ot_iso one_is_ord))), _, iso_refl⟩,
      rw [one, succ, union_empty], ext; dsimp [singleton_struct, eps_order_struct],
        refl,
      dsimp [eps_order], symmetry, rw eq_empty, intros z hz,
      simp only [mem_pair_sep, exists_prop, mem_singleton] at hz,
      rcases hz with ⟨a, az, b, bz, zab, ab⟩, subst az, subst bz,
      exact mem_empty _ ab,
    dsimp [eps_order_struct, singleton_struct], rw eq_empty,
    intros β hβ, rw [mem_inter, mem_singleton] at hβ, rcases hβ with ⟨βα, βα'⟩, subst βα',
    exact ord_mem_irrefl αord βα,
  ext,
    dsimp [add_struct, singleton_struct, succ], rw union_comm,
  dsimp [add_struct, add_rel, eps_order, singleton_struct],
  have αsub : {α} ⊆ α.succ,
    intros β βα, rw mem_singleton at βα, subst βα, rw [succ, mem_union, mem_singleton], left, refl,
  rw union_empty, apply rel_ext' (union_subset_of_subset_of_subset (subset_trans pair_sep_sub_prod (prod_subset_of_subset_of_subset self_sub_succ self_sub_succ)) (prod_subset_of_subset_of_subset self_sub_succ αsub)) pair_sep_sub_prod,
  intros x xα y yα, rw [succ, mem_union, mem_singleton] at xα yα, rw mem_union,
  cases xα,
    subst xα, cases yα,
      subst yα, split,
        rw [pair_mem_pair_sep, pair_mem_prod], rintros (⟨yy, -, -⟩|⟨yy, -⟩); exfalso; exact ord_mem_irrefl αord yy,
      rw [pair_mem_pair_sep' self_mem_succ self_mem_succ, pair_mem_pair_sep, pair_mem_prod, mem_singleton],
      finish,
    split,
      rw [pair_mem_pair_sep, pair_mem_prod], rintros (⟨yy, -, -⟩|⟨yy, -⟩); exfalso; exact ord_mem_irrefl αord yy,
    rw [pair_mem_pair_sep' self_mem_succ (ord_mem_trans αord' yα self_mem_succ), pair_mem_pair_sep, pair_mem_prod, mem_singleton],
    intro xy, exfalso, exact ord_mem_irrefl αord (ord_mem_trans αord xy yα),
  cases yα,
    subst yα, split,
      rw [pair_mem_pair_sep, pair_mem_prod, mem_singleton], rintros (⟨-, yy, -⟩|⟨-, yy⟩),
        exfalso, exact ord_mem_irrefl αord yy,
      rw pair_mem_pair_sep' (ord_mem_trans αord' xα self_mem_succ) self_mem_succ, exact xα,
    rw [pair_mem_pair_sep' (ord_mem_trans αord' xα self_mem_succ) self_mem_succ, pair_mem_pair_sep, pair_mem_prod, mem_singleton],
    finish,
  rw [pair_mem_pair_sep' xα yα, pair_mem_prod, mem_singleton,
    pair_mem_pair_sep' (ord_mem_trans αord' xα self_mem_succ) (ord_mem_trans αord' yα self_mem_succ)],
  split; finish,
end

-- Theorem 8K
theorem ord_add_assoc {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) {γ : Set} (γord : γ.is_ordinal) :
  (α.ord_add β).ord_add γ = α.ord_add (β.ord_add γ) :=
begin
  have αβord := ord_add_ord αord βord, have βγord := ord_add_ord βord γord,
  apply ord_eq_of_ord_ot_eq (ord_add_ord αβord γord) (ord_add_ord αord βγord),
  rw [ot_add_eq_add_ot αβord γord, ot_add_eq_add_ot αord βγord, ot_add_eq_add_ot αord βord, ot_add_eq_add_ot βord γord],
  exact ot_add_assoc (ord_ot_is_ot αord) (ord_ot_is_ot βord) (ord_ot_is_ot γord),
end

theorem ord_mul_assoc {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) {γ : Set} (γord : γ.is_ordinal) :
  (α.ord_mul β).ord_mul γ = α.ord_mul (β.ord_mul γ) :=
begin
  have αβord := ord_mul_ord αord βord, have βγord := ord_mul_ord βord γord,
  apply ord_eq_of_ord_ot_eq (ord_mul_ord αβord γord) (ord_mul_ord αord βγord),
  rw [ot_mul_eq_mul_ot αβord γord, ot_mul_eq_mul_ot αord βγord, ot_mul_eq_mul_ot αord βord, ot_mul_eq_mul_ot βord γord],
  exact ot_mul_assoc (ord_ot_is_ot αord) (ord_ot_is_ot βord) (ord_ot_is_ot γord),
end

theorem ord_add_mul {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) {γ : Set} (γord : γ.is_ordinal) :
  α.ord_mul (β.ord_add γ) = (α.ord_mul β).ord_add (α.ord_mul γ) :=
begin
  have βγord := ord_add_ord βord γord, have αβord := ord_mul_ord αord βord, have αγord := ord_mul_ord αord γord,
  apply ord_eq_of_ord_ot_eq (ord_mul_ord αord βγord) (ord_add_ord αβord αγord),
  rw [ot_mul_eq_mul_ot αord βγord, ot_add_eq_add_ot βord γord, ot_add_eq_add_ot αβord αγord,
    ot_mul_eq_mul_ot αord βord, ot_mul_eq_mul_ot αord γord],
  exact ot_add_mul (ord_ot_is_ot αord) (ord_ot_is_ot βord) (ord_ot_is_ot γord),
end

-- Theorem 8L (A1)
theorem ord_add_zero {α : Set} (αord : α.is_ordinal) : α.ord_add ∅ = α :=
begin
  apply ord_eq_of_ord_ot_eq (ord_add_ord αord zero_is_ord) αord,
  rw [ot_add_eq_add_ot αord zero_is_ord],
  exact ot_add_zero (ord_ot_is_ot αord),
end

theorem ord_zero_add {α : Set} (αord : α.is_ordinal) : ord_add ∅ α = α :=
begin
  apply ord_eq_of_ord_ot_eq (ord_add_ord zero_is_ord αord) αord,
  rw [ot_add_eq_add_ot zero_is_ord αord],
  exact ot_zero_add (ord_ot_is_ot αord),
end

theorem ord_mul_one {α : Set} (αord : α.is_ordinal) : α.ord_mul one = α :=
begin
  apply ord_eq_of_ord_ot_eq (ord_mul_ord αord one_is_ord) αord,
  rw [ot_mul_eq_mul_ot αord one_is_ord],
  exact ot_mul_one (ord_ot_is_ot αord),
end

theorem ord_one_mul {α : Set} (αord : α.is_ordinal) : ord_mul one α = α :=
begin
  apply ord_eq_of_ord_ot_eq (ord_mul_ord one_is_ord αord) αord,
  rw [ot_mul_eq_mul_ot one_is_ord αord],
  exact ot_one_mul (ord_ot_is_ot αord),
end

-- Theorem 8L (M1)
theorem ord_mul_zero {α : Set} (αord : α.is_ordinal) : α.ord_mul ∅ = ∅ :=
begin
  apply ord_eq_of_ord_ot_eq (ord_mul_ord αord zero_is_ord) zero_is_ord,
  rw [ot_mul_eq_mul_ot αord zero_is_ord],
  exact ot_mul_zero (ord_ot_is_ot αord),
end

theorem ord_zero_mul {α : Set} (αord : α.is_ordinal) : ord_mul ∅ α = ∅ :=
begin
  apply ord_eq_of_ord_ot_eq (ord_mul_ord zero_is_ord αord) zero_is_ord,
  rw [ot_mul_eq_mul_ot zero_is_ord αord],
  exact ot_zero_mul (ord_ot_is_ot αord),
end

-- Theorem 8L (A2)
theorem ord_add_succ {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  α.ord_add β.succ = (α.ord_add β).succ :=
by rw [←ord_add_one_eq_succ βord, ←ord_add_assoc αord βord one_is_ord, ord_add_one_eq_succ (ord_add_ord αord βord)]

-- Theorem 8L (M2)
theorem ord_mul_succ {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  α.ord_mul β.succ = (α.ord_mul β).ord_add α :=
by rw [←ord_add_one_eq_succ βord, ord_add_mul αord βord one_is_ord, ord_mul_one αord]

structure end_extension (R S : struct) : Prop :=
(fld : R.fld ⊆ S.fld)
(rel : R.rel ⊆ S.rel)
(ext : ∀ {r : Set}, r ∈ R.fld → ∀ {s : Set}, s ∈ S.fld \ R.fld → r.pair s ∈ S.rel)

lemma L8M_lemma {C : Set} (hC : ∀ ⦃R : Set⦄, R ∈ C → ∃ S : struct, S.fld.well_order S.rel ∧ R = struct_to_set S) :
  let A := (repl_img fst C).Union in
  (repl_img snd C).Union ⊆ A.prod A :=
begin
  dsimp, intro z, simp only [mem_Union, exists_prop, mem_repl_img],
  rintro ⟨R', ⟨S, RC, RS⟩, zR⟩, subst RS, rcases hC RC with ⟨R, Rwell, RR⟩, subst RR,
  rw set_snd_eq_rel at zR,
  have zAA := R.is_rel zR, rw mem_prod at zAA, rcases zAA with ⟨a, aA, b, bA, zab⟩, subst zab,
  simp only [pair_mem_prod, mem_Union, exists_prop, mem_repl_img],
  refine ⟨⟨_, ⟨_, RC, _⟩, aA⟩, _, ⟨_, RC, _⟩, bA⟩; rw set_fst_eq_fld,
end

lemma seg_eq_of_ext {R : struct} (Rlin : R.fld.lin_order R.rel) {S : struct} (Slin : S.fld.lin_order S.rel)
  (RS : end_extension R S) {a : Set} (aA : a ∈ R.fld) : S.rel.seg a = R.rel.seg a :=
begin
  apply ext, simp only [mem_seg], intro x, split,
    intro xa,
    have xA : x ∈ R.fld, apply classical.by_contradiction, intro xA,
      refine not_lt_and_gt_part (part_order_of_lin_order Slin) ⟨xa, RS.ext aA _⟩,
      rw mem_diff, refine ⟨_, xA⟩, replace xa := Slin.rel xa, rw pair_mem_prod at xa, exact xa.left,
    have xna : x ≠ a, intro xea, subst xea, exact Slin.irrefl xa,
    cases Rlin.conn xA aA xna with xRa aRx,
      exact xRa,
    exfalso, exact not_lt_and_gt_part (part_order_of_lin_order Slin) ⟨xa, RS.rel aRx⟩,
  apply RS.rel,
end

lemma L8M {C : Set.{u}} (hC : ∀ ⦃R : Set⦄, R ∈ C → ∃ S : struct, S.fld.well_order S.rel ∧ R = struct_to_set S)
  (hext : ∀ {R : struct}, struct_to_set R ∈ C → ∀ {S : struct}, struct_to_set S ∈ C → end_extension R S ∨ end_extension S R) :
  let W : struct := ⟨(repl_img fst C).Union, (repl_img snd C).Union, L8M_lemma hC⟩
  in W.fld.well_order W.rel ∧ eps_img W = (repl_img (eps_img ∘ set_to_struct) C).Union :=
begin
  have memC : ∀ {R : struct}, struct_to_set R ∈ C → R.fld.well_order R.rel,
    intros R RC, rcases hC RC with ⟨S, Swell, RS⟩, rw struct_to_set_oto RS, exact Swell,
  dsimp, set W : struct := ⟨(repl_img fst C).Union, (repl_img snd C).Union, L8M_lemma hC⟩,
  let E := (repl_img (eps_img_fun ∘ set_to_struct) C).Union,
  have ord : (repl_img (eps_img ∘ set_to_struct) C).Union.is_ordinal,
    apply Union_ords_is_ord, apply of_repl_img, intros R RC, rw function.comp_app,
    rcases hC RC with ⟨S, Swell, RS⟩, subst RS, rw struct_set_struct_eq_self,
    exact eps_img_ord Swell,
  have Eiso : E.isomorphism W (repl_img (eps_img ∘ set_to_struct) C).Union.eps_order_struct,
    have Xch : (repl_img (eps_img_fun ∘ set_to_struct) C).is_chain,
    { intros F hF G hG, simp only [mem_repl_img, function.comp_app] at hF hG,
      rcases hF with ⟨R', RC, FR⟩, subst FR, rcases hG with ⟨S', SC, GS⟩, subst GS,
      obtain ⟨R, Rwell, RR⟩ := hC RC, subst RR, obtain ⟨S, Swell, SS⟩ := hC SC, subst SS,
      simp only [struct_set_struct_eq_self], cases hext RC SC with RS RS,
      left, rotate, rename [R → S, Rwell → Swell, RC → SC, S → R, Swell → Rwell, SC → RC], right, rotate,
      all_goals {
        have h : eps_img_fun R = (eps_img_fun S).restrict R.fld,
          apply fun_ext (eps_img_fun_onto Rwell).left (restrict_is_function (eps_img_fun_onto Swell).left),
            rw (eps_img_fun_onto Rwell).right.left, symmetry, apply restrict_dom,
            rw (eps_img_fun_onto Swell).right.left, exact RS.fld,
          let X := {x ∈ R.fld | (eps_img_fun R).fun_value x = ((eps_img_fun S).restrict R.fld).fun_value x},
          suffices XA : X = R.fld,
            intros x xA, rw [(eps_img_fun_onto Rwell).right.left, ←XA, mem_sep] at xA,
            exact xA.right,
          apply transfinite_ind Rwell sep_subset, intros a aA ind,
          rw mem_sep, refine ⟨aA, _⟩, rw eps_img_fun_value_img Rwell aA,
          have sub : R.fld ⊆ (eps_img_fun S).dom, rw (eps_img_fun_onto Swell).right.left, exact RS.fld,
          rw [restrict_fun_value (eps_img_fun_onto Swell).left sub aA,
            eps_img_fun_value_img Swell (RS.fld aA)],
          rw seg_eq_of_ext Rwell.lin Swell.lin RS aA,
          refine img_fun_eq (eps_img_fun_onto Rwell).left _ (eps_img_fun_onto Swell).left _ _,
              rw (eps_img_fun_onto Rwell).right.left, exact seg_sub R.is_rel aA,
            rw (eps_img_fun_onto Swell).right.left, exact subset_trans (seg_sub R.is_rel aA) RS.fld,
          intros x xa, specialize ind xa, rw mem_sep at ind, rcases ind with ⟨xA, fgx⟩,
          rw restrict_fun_value (eps_img_fun_onto Swell).left sub xA at fgx, exact fgx,
        rw h, exact restrict_subset, }, },
    have Xfun : ∀ ⦃f : Set⦄, f ∈ (repl_img (eps_img_fun ∘ set_to_struct) C) → f.is_function,
      simp only [mem_repl_img, function.comp_app], rintros f ⟨R', RC, fR⟩, subst fR,
      obtain ⟨R, Rwell, RR⟩ := hC RC, subst RR,
      rw struct_set_struct_eq_self, exact (eps_img_fun_onto Rwell).left,
    have Xoto : ∀ ⦃f : Set⦄, f ∈ (repl_img (eps_img_fun ∘ set_to_struct) C) → f.one_to_one,
      simp only [mem_repl_img, function.comp_app], rintros f ⟨R', RC, fR⟩, subst fR,
      obtain ⟨R, Rwell, RR⟩ := hC RC, subst RR,
      rw struct_set_struct_eq_self, exact eps_img_fun_oto Rwell,
    have Eonto := Union_chain_onto Xch Xfun, have Eoto := Union_chain_oto Xch Xoto,
    have dom : (repl_img dom (repl_img (eps_img_fun ∘ set_to_struct) C)).Union = W.fld,
      dsimp [W], rw repl_img_comp, congr' 1, apply repl_img_ext,
      intros R' RC, simp only [function.comp_app],
      obtain ⟨R, Rwell, RR⟩ := hC RC, subst RR,
      rw [set_fst_eq_fld, struct_set_struct_eq_self, (eps_img_fun_onto (memC RC)).right.left],
    have ran : (repl_img ran (repl_img (eps_img_fun ∘ set_to_struct) C)).Union = (repl_img (eps_img ∘ set_to_struct) C).Union.eps_order_struct.fld,
      rw [eps_order_struct_fld, repl_img_comp], refl,
    have hE : ∀ {R : struct}, struct_to_set R ∈ C → ∀ {x : Set}, x ∈ R.fld → E.fun_value x = (eps_img_fun R).fun_value x,
      intros R RC x xR, apply Union_chain_fun_value Xch Xfun,
        rw mem_repl_img, refine ⟨_, RC, _⟩, rw [function.comp_app, struct_set_struct_eq_self],
      rw (eps_img_fun_onto (memC RC)).right.left, exact xR,
    rw [dom, ran] at Eonto, apply iso_of_corr' ⟨Eonto, Eoto⟩,
    dsimp [W], intros x y,
    calc
      x.pair y ∈ (repl_img snd C).Union ↔ ∃ S : struct.{u}, struct_to_set S ∈ C ∧ x.pair y ∈ S.rel : begin
        simp only [mem_Union, exists_prop, mem_repl_img, ←exists_and_distrib_right, and_assoc],
        rw exists_comm, simp only [exists_and_distrib_left, exists_eq_left, and_comm], split,
          rintro ⟨R, RC, xyR⟩, obtain ⟨S, Swell, RS⟩ := hC RC, subst RS, rw set_snd_eq_rel at xyR,
          exact ⟨_, RC, xyR⟩,
        rintro ⟨S, SC, xyS⟩, refine ⟨_, SC, _⟩, rw set_snd_eq_rel, exact xyS,
      end
      ... ↔ ∃ S : struct, struct_to_set S ∈ C ∧ x ∈ S.fld ∧ y ∈ S.fld ∧ ((eps_img_fun S).fun_value x).pair ((eps_img_fun S).fun_value y) ∈ (eps_img S).eps_order :
      begin
        apply exists_congr, intro R, apply and_congr_right, intro RC,
        apply iso_iso (eps_img_iso (memC RC)),
      end
      ... ↔ x ∈ (repl_img fst C).Union ∧ y ∈ (repl_img fst C).Union ∧ (E.fun_value x).pair (E.fun_value y) ∈ (repl_img (eps_img ∘ set_to_struct) C).Union.eps_order :
      begin
        split,
          rintro ⟨R, RC, xR, yR, fxy⟩,
          have xD : x ∈ (repl_img fst C).Union, simp only [mem_Union, exists_prop, mem_repl_img],
            refine ⟨_, ⟨_, RC, _⟩, xR⟩, rw set_fst_eq_fld,
          have yD : y ∈ (repl_img fst C).Union, simp only [mem_Union, exists_prop, mem_repl_img],
            refine ⟨_, ⟨_, RC, _⟩, yR⟩, rw set_fst_eq_fld,
          have Ex : E.fun_value x ∈ E.ran, apply fun_value_def'' Eonto.left, rw Eonto.right.left, exact xD,
          have Ey : E.fun_value y ∈ E.ran, apply fun_value_def'' Eonto.left, rw Eonto.right.left, exact yD,
          have ex : (eps_img_fun R).fun_value x ∈ (eps_img_fun R).ran, apply fun_value_def'' (eps_img_fun_onto (memC RC)).left,
            rw (eps_img_fun_onto (memC RC)).right.left, exact xR,
          have ey : (eps_img_fun R).fun_value y ∈ (eps_img_fun R).ran, apply fun_value_def'' (eps_img_fun_onto (memC RC)).left,
            rw (eps_img_fun_onto (memC RC)).right.left, exact yR,
          rw Eonto.right.right at Ex Ey, dsimp at Ex Ey, rw (eps_img_fun_onto (memC RC)).right.right at ex ey,
          rw pair_mem_eps_order' ex ey at fxy, rw [pair_mem_eps_order' Ex Ey, hE RC xR, hE RC yR],
          exact ⟨xD, yD, fxy⟩,
        rintro ⟨xD, yD, Exy⟩,
        have Ex : E.fun_value x ∈ E.ran, apply fun_value_def'' Eonto.left, rw Eonto.right.left, exact xD,
        have Ey : E.fun_value y ∈ E.ran, apply fun_value_def'' Eonto.left, rw Eonto.right.left, exact yD,
        rw Eonto.right.right at Ex Ey, dsimp at Ex Ey, rw pair_mem_eps_order' Ex Ey at Exy,
        simp only [mem_Union, exists_prop, mem_repl_img] at xD yD,
        rcases xD with ⟨A, ⟨R', RC, AR⟩, xA⟩, subst AR, rcases yD with ⟨B, ⟨S', SC, BS⟩, yB⟩, subst BS,
        obtain ⟨R, Rwell, RR⟩ := hC RC, obtain ⟨S, Swell, SS⟩ := hC SC, subst RR, subst SS,
        rw set_fst_eq_fld at xA yB,
        cases hext RC SC with RS SR,
          have xB := RS.fld xA,
          refine ⟨S, SC, xB, yB, _⟩,
          rw [pair_mem_eps_order' (fun_value_mem_eps_img (memC SC) xB) (fun_value_mem_eps_img (memC SC) yB),
            ←hE SC xB, ←hE SC yB],
          exact Exy,
        have yA := SR.fld yB,
        refine ⟨R, RC, xA, yA, _⟩,
        rw [pair_mem_eps_order' (fun_value_mem_eps_img (memC RC) xA) (fun_value_mem_eps_img (memC RC) yA),
          ←hE RC xA, ←hE RC yA],
        exact Exy,
      end,
  refine ⟨_, eps_img_eq_of_iso_ord ord ⟨_, Eiso⟩⟩,
    change W.fld.well_order W.rel, exact well_order_iso (iso_symm ⟨_, Eiso⟩) (ordinal_well_ordered' ord),
end

lemma prod_union_eq_Union_prod {X Y : Set} : Y.Union.prod X = (repl_img (λ z, z.prod X) Y).Union :=
begin
  have h : ∀ ⦃z : Set⦄, z ∈ repl_img (λ z, z.prod X) Y → z.is_rel,
    intros z hz, rw mem_repl_img at hz, rcases hz with ⟨x, xy, zXx⟩, subst zXx, exact prod_is_rel,
  apply rel_ext prod_is_rel (Union_is_rel h),
  simp only [pair_mem_prod, mem_Union, exists_prop, mem_repl_img], intros x y, split,
    rintro ⟨⟨z, zY, xz⟩, yX⟩, refine ⟨_, ⟨_, zY, rfl⟩, _⟩, rw pair_mem_prod,
    exact ⟨xz, yX⟩,
  rintro ⟨P, ⟨z, zY, PzX⟩, xyP⟩, subst PzX, rw pair_mem_prod at xyP,
  exact ⟨⟨_, zY, xyP.left⟩, xyP.right⟩,
end

lemma union_Union_repl_img {f : Set → Set} {X Y : Set} (Yin : Y.inhab) : X ∪ (repl_img f Y).Union = (repl_img (λ z, X ∪ f z) Y).Union :=
begin
  apply ext, simp only [mem_union, mem_Union, exists_prop, mem_repl_img], intro z, split,
    rintro (zX|⟨fx, ⟨y, yY, fxfx⟩, zfx⟩),
      rcases Yin with ⟨c, cY⟩, refine ⟨_, ⟨_, cY, rfl⟩, _⟩, rw mem_union, left, exact zX,
    subst fxfx, refine ⟨_, ⟨_, yY, rfl⟩, _⟩, rw mem_union, right, exact zfx,
  rintro ⟨Xfx, ⟨y, yY, XfxXfx⟩, zXfx⟩, subst XfxXfx, rw mem_union at zXfx, rcases zXfx with (zX|zfy),
    left, exact zX,
  right, exact ⟨_, ⟨_, yY, rfl⟩, zfy⟩,
end

lemma pair_mem_pair_sep_of {q : Set → Set → Prop} {C D x y : Set} (xy : x.pair y ∈ pair_sep q C D)
  {A : Set} (xA : x ∈ A) {B : Set} (yB : y ∈ B) : x.pair y ∈ pair_sep q A B :=
begin
  rw pair_mem_pair_sep at xy ⊢, rcases xy with ⟨-, -, qxy⟩, exact ⟨xA, yB, qxy⟩,
end

noncomputable def ord_max (α β : Set) : Set :=
if α ∈ β then β else α

lemma ord_max_of_lt {α β : Set} (αβ : α ∈ β) : α.ord_max β = β :=
by rw [ord_max, if_pos αβ]

lemma ord_max_of_not_lt {α β : Set} (αβ : α ∉ β) : α.ord_max β = α :=
by rw [ord_max, if_neg αβ]

lemma ord_max_prop {p : Set → Prop} {α : Set} (pα : p α) {β : Set} (pβ : p β) : p (α.ord_max β) := ite_prop pβ pα
lemma ord_max_ord {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) : (α.ord_max β).is_ordinal :=
ord_max_prop αord βord

lemma ord_max_le_left {α β : Set} : α ≤ α.ord_max β :=
begin
  by_cases αβ : α ∈ β,
    rw ord_max_of_lt αβ, left, exact αβ,
  rw ord_max_of_not_lt αβ, right, refl,
end

lemma ord_max_le_right {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) : β ≤ α.ord_max β :=
begin
  by_cases αβ : α ∈ β,
    rw ord_max_of_lt αβ, right, refl,
  rw ord_max_of_not_lt αβ, rw ←ord_not_lt_iff_le αord βord, exact αβ,
end

lemma ord_max_sub_left {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) : α ⊆ α.ord_max β :=
begin
  rw ←ord_le_iff_sub αord (ord_max_ord αord βord), exact ord_max_le_left,
end

lemma ord_max_sub_right {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) : β ⊆ α.ord_max β :=
begin
  rw ←ord_le_iff_sub βord (ord_max_ord αord βord), exact ord_max_le_right αord βord,
end

-- Theorem 8L (A3)
theorem ord_add_limit {α : Set} (αord : α.is_ordinal) {γ : Set} (γord : γ.limit_ord) :
  α.ord_add γ = (repl_img α.ord_add γ).Union :=
begin
  have h : ∀ ⦃β : Set⦄, β ∈ repl_img α.ord_add γ → β.is_ordinal,
    intros β hβ, rw mem_repl_img at hβ, rcases hβ with ⟨δ, δγ, βαδ⟩, subst βαδ,
    exact ord_add_ord αord (ord_of_mem_ord γord.ord δγ),
  apply ord_eq_of_ord_ot_eq (ord_add_ord αord γord.ord) (Union_ords_is_ord h),
  rw ot_add_eq_add_ot αord γord.ord, dsimp [ord_ot],
  have h₂ := it_add_eq_lex (ordinal_well_ordered' αord).lin (ordinal_well_ordered' γord.ord).lin,
  dsimp at h₂, rw h₂, clear h₂,
  rw [limit_ord_eq_Union γord, prod_union_eq_Union_prod, union_Union_repl_img (inhabited_of_ne_empty γord.ne)],
  set C := (repl_img (λ β, let D := α.prod {∅} ∪ β.prod {one} in struct_to_set
    ⟨D, pair_sep (λ x y, x.snd ∈ y.snd ∨ x.snd = y.snd ∧ (x.snd = ∅ ∧ x.fst.pair y.fst ∈ α.eps_order ∨ x.snd = one ∧ x.fst.pair y.fst ∈ β.eps_order)) D D, pair_sep_sub_prod⟩) γ),
  have hC: ∀ ⦃R : Set⦄, R ∈ C → ∃ S : struct, S.fld.well_order S.rel ∧ R = struct_to_set S,
    intros R RC, simp only [C, mem_repl_img] at RC, rcases RC with ⟨β, βγ, Re⟩, subst Re, refine ⟨_, _, rfl⟩,
    dsimp, exact lex_well_order αord (ord_of_mem_ord γord.ord βγ),
  let W : struct := ⟨(repl_img fst C).Union, (repl_img snd C).Union, L8M_lemma hC⟩,
  have h₃ : (⟨(repl_img (λ β, α.prod {∅} ∪ β.prod {one}) γ).Union,
    pair_sep
          (λ x y,
             x.snd ∈ y.snd ∨
               x.snd = y.snd ∧
                 (x.snd = ∅ ∧ x.fst.pair y.fst ∈ α.eps_order ∨
                    x.snd = one ∧ x.fst.pair y.fst ∈ γ.Union.eps_order))
          (repl_img (λ β, α.prod {∅} ∪ β.prod {one}) γ).Union
          (repl_img (λ β, α.prod {∅} ∪ β.prod {one}) γ).Union,
    pair_sep_sub_prod⟩ : struct) = W,
    have de : (repl_img (λ (β : Set), α.prod {∅} ∪ β.prod {one}) γ).Union = (repl_img fst C).Union,
      congr' 1, apply ext, simp only [mem_repl_img], intro A, split,
        rintro ⟨β, βγ, Ae⟩, subst Ae, refine ⟨_, ⟨_, βγ, rfl⟩, _⟩, rw set_fst_eq_fld,
      rintro ⟨S, ⟨β, βγ, Se⟩, AS⟩, subst Se, rw set_fst_eq_fld at AS, exact ⟨_, βγ, AS⟩,
    ext,
      dsimp, exact de,
    dsimp, apply @rel_ext' (repl_img fst C).Union (repl_img fst C).Union,
        rw de, exact pair_sep_sub_prod,
      refine rel_sub (Union_is_rel _) _,
        simp only [mem_repl_img, C], rintros R ⟨S, ⟨β, βγ, Se⟩, RS⟩, subst Se, subst RS,
        rw set_snd_eq_rel, dsimp, exact pair_sep_is_rel,
      simp only [mem_Union, exists_prop, pair_mem_prod, mem_repl_img],
      rintros x y ⟨R, ⟨S, ⟨β, βγ, Se⟩, RS⟩, xyR⟩, subst Se, subst RS,
      rw set_snd_eq_rel at xyR, dsimp at xyR,
      have xy := pair_sep_sub_prod xyR,
      rw pair_mem_prod at xy,
      refine ⟨⟨_, ⟨_, ⟨_, βγ, rfl⟩, rfl⟩, _⟩, _, ⟨_, ⟨_, βγ, rfl⟩, rfl⟩, _⟩; rw set_fst_eq_fld; dsimp,
        exact xy.left,
      exact xy.right,
    intros x hx y hy, split,
      simp only [mem_Union, exists_prop, mem_repl_img] at hx hy,
      rcases hx with ⟨A, ⟨S, ⟨β, βγ, Se⟩, AS⟩, xA⟩, subst Se, subst AS, rw set_fst_eq_fld at xA, dsimp at xA,
      rcases hy with ⟨A', ⟨S', ⟨β', βγ', Se'⟩, AS'⟩, yA⟩, subst Se', subst AS', rw set_fst_eq_fld at yA, dsimp at yA,
      intro xy,
      simp only [mem_Union, exists_prop, mem_repl_img],
      refine ⟨_, ⟨_, ⟨_, @ord_max_prop (λ δ, δ ∈ γ) _ βγ _ βγ', rfl⟩, rfl⟩, _⟩,
      rw set_snd_eq_rel, dsimp,
      have βord := ord_of_mem_ord γord.ord βγ, have βord' := ord_of_mem_ord γord.ord βγ',
      have sub : α.prod {∅} ∪ β.prod {one} ⊆ α.prod {∅} ∪ (β.ord_max β').prod {one} :=
        union_subset_of_subset_of_subset subset_union_left (subset_union_of_subset_right (prod_subset_of_subset_of_subset (ord_max_sub_left βord βord') subset_self)),
      have sub' : α.prod {∅} ∪ β'.prod {one} ⊆ α.prod {∅} ∪ (β.ord_max β').prod {one} :=
        union_subset_of_subset_of_subset subset_union_left (subset_union_of_subset_right (prod_subset_of_subset_of_subset (ord_max_sub_right βord βord') subset_self)),
      have xA'' : x ∈ α.prod {∅} ∪ (β.ord_max β').prod {one} := sub xA,
      have yA'' : y ∈ α.prod {∅} ∪ (β.ord_max β').prod {one} := sub' yA,
      have ord_max_sub : β.ord_max β' ⊆ γ, rw ←ord_le_iff_sub (ord_max_ord βord βord') γord.ord, left,
        exact @ord_max_prop _ β βγ β' βγ',
      have xA' : x ∈ α.prod {∅} ∪ γ.prod {one} :=
        union_subset_of_subset_of_subset subset_union_left (subset_union_of_subset_right (prod_subset_of_subset_of_subset ord_max_sub subset_self)) xA'',
      have yA' : y ∈ α.prod {∅} ∪ γ.prod {one} :=
        union_subset_of_subset_of_subset subset_union_left (subset_union_of_subset_right (prod_subset_of_subset_of_subset ord_max_sub subset_self)) yA'',
      rw ←limit_ord_eq_Union γord at xy,
      rw pair_mem_pair_sep' xA'' yA'',
      obtain (⟨a, aα, xaz, b, bγ, ybz⟩|(⟨a, aα, xaz, b, bα, ybz, ab⟩|⟨a, aγ, xaz, b, bγ, ybz, ab⟩)) :=
        @pair_mem_lex α.eps_order_struct γ.eps_order_struct _ _ (pair_mem_pair_sep_of xy xA' yA');
      subst xaz; subst ybz; simp only [fst_congr, snd_congr],
          left, rw [one, succ, union_empty, mem_singleton],
        right, exact ⟨rfl, or.inl ⟨rfl, ab⟩⟩,
      right, refine ⟨rfl, or.inr ⟨rfl, _⟩⟩,
      rw eps_order_struct_fld at aγ bγ,
      rw [eps_order_struct_rel, pair_mem_eps_order' aγ bγ] at ab,
      simp only [mem_union, pair_mem_prod] at xA yA,
      rcases xA with (⟨-, h⟩|⟨aβ, -⟩),
        exfalso, rw mem_singleton at h, exact zero_ne_one h.symm,
      rcases yA with (⟨-, h⟩|⟨bβ, -⟩),
        exfalso, rw mem_singleton at h, exact zero_ne_one h.symm,
      rw pair_mem_eps_order' (ord_lt_of_lt_of_le (ord_max_ord βord βord') aβ ord_max_le_left) (ord_lt_of_lt_of_le (ord_max_ord βord βord') bβ (ord_max_le_right βord βord')),
      exact ab,
    intro xy, rw [de, pair_mem_pair_sep' hx hy],
    simp only [mem_Union, exists_prop, mem_repl_img] at xy,
    rcases xy with ⟨R, ⟨S, ⟨β, βγ, Se⟩, RS⟩, xyR⟩, subst Se, subst RS,
    simp only [set_snd_eq_rel, pair_mem_pair_sep] at xyR, rw ←limit_ord_eq_Union γord,
    rcases xyR with ⟨-, -, (xy|⟨xy, (⟨x₂, xy₁⟩|⟨x₂, xy₁⟩)⟩)⟩,
        left, exact xy,
      right, exact ⟨xy, or.inl ⟨x₂, xy₁⟩⟩,
    right, refine ⟨xy, or.inr ⟨x₂, eps_order_sub (ord_of_mem_ord γord.ord βγ) γord.ord (or.inl βγ) xy₁⟩⟩,
  rw h₃, clear h₃,
  have ext' : ∀ {R : struct}, struct_to_set R ∈ C → ∀ {S : struct}, struct_to_set S ∈ C → end_extension R S ∨ end_extension S R,
    intros R hR S hS, simp only [mem_repl_img] at hR hS,
    rcases hR with ⟨β, βγ, hR⟩, replace hR := struct_to_set_oto hR, subst hR,
    rcases hS with ⟨δ, δγ, hS⟩, replace hS := struct_to_set_oto hS, subst hS,
    have βord := ord_of_mem_ord γord.ord βγ, have δord := ord_of_mem_ord γord.ord δγ,
    have h₄ : ∀ {X Y Z : Set}, (X ∪ Y) \ (X ∪ Z) = (Y \ Z) \ X, intros X Y Z, apply ext,
      simp only [mem_diff, mem_union], tauto,
    cases ord_conn' βord δord with βδ δβ,
      have sub : α.prod {∅} ∪ β.prod {one} ⊆ α.prod {∅} ∪ δ.prod {one},
      refine union_subset_of_subset_of_subset subset_union_left (subset_union_of_subset_right (prod_subset_of_subset_of_subset _ subset_self)),
      rw ←ord_le_iff_sub βord δord, exact βδ,
      left, split,
          dsimp, refine union_subset_of_subset_of_subset subset_union_left (subset_union_of_subset_right (prod_subset_of_subset_of_subset _ subset_self)),
          rw ←ord_le_iff_sub βord δord, exact βδ,
        dsimp, apply rel_sub pair_sep_is_rel, intros x y xy,
        have xy' := pair_sep_sub_prod xy, rw pair_mem_prod at xy',
        rw pair_mem_pair_sep' (sub xy'.left) (sub xy'.right),
        obtain (⟨a, aα, xaz, b, bβ, ybz⟩|(⟨a, aα, xaz, b, bβ, ybz, ab⟩|⟨a, aα, xaz, b, bβ, ybz, ab⟩)) := @pair_mem_lex α.eps_order_struct β.eps_order_struct _ _ xy;
        subst xaz; subst ybz; simp only [fst_congr, snd_congr]; rw eps_order_struct_fld at aα bβ,
            left, rw [one, succ, union_empty, mem_singleton],
          right, rw [eps_order_struct_rel, pair_mem_eps_order' aα bβ] at ab,
          rw pair_mem_eps_order' aα bβ, exact ⟨rfl, or.inl ⟨rfl, ab⟩⟩,
        right, rw [eps_order_struct_rel, pair_mem_eps_order' aα bβ] at ab,
        rw pair_mem_eps_order' (ord_lt_of_lt_of_le δord aα βδ) (ord_lt_of_lt_of_le δord bβ βδ), exact ⟨rfl, or.inr ⟨rfl, ab⟩⟩,
      dsimp, intros x hx y hy, have hy' := hy, rw h₄ at hy', rw mem_diff at hy,
      rw pair_mem_pair_sep' (sub hx) hy.left,
      simp only [mem_union, mem_prod, exists_prop, mem_diff, mem_singleton] at hx hy',
      rcases hx with (⟨a, ha, z, hz, xaz⟩|⟨a, ha, z, hz, xaz⟩); subst xaz; subst hz;
      rcases hy' with ⟨⟨⟨b, hb, w, hw, ybw⟩, h₅⟩, h₆⟩; subst ybw; subst hw;
      simp only [fst_congr, snd_congr],
      { left, rw [one, succ, union_empty, mem_singleton], },
      { right, rw pair_mem_eps_order' (ord_lt_of_lt_of_le δord ha βδ) hb,
        refine ⟨rfl, or.inr ⟨rfl, _⟩⟩, rw ←ord_not_le_iff_lt (ord_of_mem_ord δord hb) (ord_of_mem_ord βord ha),
        intro ba, exact h₅ ⟨_, ord_lt_of_le_of_lt βord ba ha, _, rfl, rfl⟩, },
    have sub : α.prod {∅} ∪ δ.prod {one} ⊆ α.prod {∅} ∪ β.prod {one},
      refine union_subset_of_subset_of_subset subset_union_left (subset_union_of_subset_right (prod_subset_of_subset_of_subset _ subset_self)),
      rw ←ord_le_iff_sub δord βord, exact δβ,
    right, split,
        dsimp, refine union_subset_of_subset_of_subset subset_union_left (subset_union_of_subset_right (prod_subset_of_subset_of_subset _ subset_self)),
        rw ←ord_le_iff_sub δord βord, exact δβ,
      dsimp, apply rel_sub pair_sep_is_rel, intros x y xy,
      have xy' := pair_sep_sub_prod xy, rw pair_mem_prod at xy',
      rw pair_mem_pair_sep' (sub xy'.left) (sub xy'.right),
      obtain (⟨a, aα, xaz, b, bβ, ybz⟩|(⟨a, aα, xaz, b, bβ, ybz, ab⟩|⟨a, aα, xaz, b, bβ, ybz, ab⟩)) := @pair_mem_lex α.eps_order_struct δ.eps_order_struct _ _ xy;
      subst xaz; subst ybz; simp only [fst_congr, snd_congr]; rw eps_order_struct_fld at aα bβ,
          left, rw [one, succ, union_empty, mem_singleton],
        right, rw [eps_order_struct_rel, pair_mem_eps_order' aα bβ] at ab,
        rw pair_mem_eps_order' aα bβ, exact ⟨rfl, or.inl ⟨rfl, ab⟩⟩,
      right, rw [eps_order_struct_rel, pair_mem_eps_order' aα bβ] at ab,
      rw pair_mem_eps_order' (ord_lt_of_lt_of_le βord aα δβ) (ord_lt_of_lt_of_le βord bβ δβ), exact ⟨rfl, or.inr ⟨rfl, ab⟩⟩,
    dsimp, intros x hx y hy, have hy' := hy, rw h₄ at hy', rw mem_diff at hy,
    rw pair_mem_pair_sep' (sub hx) hy.left,
    simp only [mem_union, mem_prod, exists_prop, mem_diff, mem_singleton] at hx hy',
    rcases hx with (⟨a, ha, z, hz, xaz⟩|⟨a, ha, z, hz, xaz⟩); subst xaz; subst hz;
    rcases hy' with ⟨⟨⟨b, hb, w, hw, ybw⟩, h₅⟩, h₆⟩; subst ybw; subst hw;
    simp only [fst_congr, snd_congr],
    { left, rw [one, succ, union_empty, mem_singleton], },
    { right, rw pair_mem_eps_order' (ord_lt_of_lt_of_le βord ha δβ) hb,
      refine ⟨rfl, or.inr ⟨rfl, _⟩⟩, rw ←ord_not_le_iff_lt (ord_of_mem_ord βord hb) (ord_of_mem_ord δord ha),
      intro ba, exact h₅ ⟨_, ord_lt_of_le_of_lt δord ba ha, _, rfl, rfl⟩, },
  obtain ⟨Wwell, We⟩ := L8M hC @ext',
  let D := (repl_img (eps_img ∘ set_to_struct) C).Union,
  rw iso_type_eq_iff_iso, apply iso_trans (eps_img_isomorphic Wwell), rw We, apply iso_of_eq, congr' 2,
  have h₂ : ∀ {β : Set}, β ∈ γ → (eps_img ∘ set_to_struct)
    (struct_to_set
       {fld := α.prod {∅} ∪ β.prod {one},
        rel := pair_sep
                 (λ (x y : Set),
                    x.snd ∈ y.snd ∨
                      x.snd = y.snd ∧
                        (x.snd = ∅ ∧ x.fst.pair y.fst ∈ α.eps_order ∨
                           x.snd = one ∧ x.fst.pair y.fst ∈ β.eps_order))
                 (α.prod {∅} ∪ β.prod {one})
                 (α.prod {∅} ∪ β.prod {one}),
        is_rel := _}) =
  α.ord_add β, intros β βγ,
    have βord := ord_of_mem_ord γord.ord βγ,
    rw [function.comp_app _ _, struct_set_struct_eq_self _],
    apply ord_eq_of_ord_ot_eq (eps_img_ord (lex_well_order αord βord)) (ord_add_ord αord βord),
    rw ot_add_eq_add_ot αord βord, dsimp [ord_ot],
    have h₁ := it_add_eq_lex (ordinal_well_ordered' αord).lin (ordinal_well_ordered' βord).lin,
    dsimp at h₁, rw h₁, clear h₁, rw iso_type_eq_iff_iso, apply iso_symm,
    apply eps_img_isomorphic (lex_well_order αord βord),
  apply ext, rw ←limit_ord_eq_Union γord, simp only [mem_repl_img], intro δ, split,
    rintro ⟨R, ⟨β, βγ, Re⟩, δR⟩, refine ⟨_, βγ, _⟩, subst Re, subst δR,
    exact h₂ βγ,
  rintro ⟨β, βγ, δαβ⟩, subst δαβ, refine ⟨_, ⟨_, βγ, rfl⟩, (h₂ βγ).symm⟩,
end

-- Theorem 8L (M3)
theorem ord_mul_limit {α : Set} (αord : α.is_ordinal) {γ : Set} (γord : γ.limit_ord) :
  α.ord_mul γ = (repl_img α.ord_mul γ).Union :=
begin
  refine ord_eq_of_ord_ot_eq (ord_mul_ord αord γord.ord) (Union_ords_is_ord _) _,
    intros αβ, rw mem_repl_img, rintro ⟨β, βγ, αβαβ⟩, subst αβαβ,
    exact ord_mul_ord αord (ord_of_mem_ord γord.ord βγ),
  rw [ot_mul_eq_mul_ot αord γord.ord, ord_ot, ord_ot,
    it_mul (ordinal_well_ordered' αord).lin (ordinal_well_ordered' γord.ord).lin],
  nth_rewrite 0 limit_ord_eq_Union γord,
  have h₁ : ∀ ⦃β : Set⦄, β ∈ γ → α.ord_mul β = (eps_img ∘ (mul_struct α.eps_order_struct) ∘ eps_order_struct) β,
    simp only [function.comp_app], intros β βγ,
    have βord := ord_of_mem_ord γord.ord βγ,
    apply ord_eq_of_ord_ot_eq (ord_mul_ord αord βord) (eps_img_ord (mul_struct_well_order αord βord)),
    rw [ot_mul_eq_mul_ot αord βord, ord_ot, ord_ot, ord_ot,
      it_mul (ordinal_well_ordered' αord).lin (ordinal_well_ordered' βord).lin,
      iso_type_eq_iff_iso],
    exact eps_img_isomorphic (mul_struct_well_order αord βord),
  rw repl_img_ext h₁, dsimp,
  let C := repl_img (struct_to_set ∘ (mul_struct α.eps_order_struct) ∘ eps_order_struct) γ,
  have hC : ∀ ⦃R : Set⦄, R ∈ C → ∃ S : struct, S.fld.well_order S.rel ∧ R = struct_to_set S,
    intros R RC, simp only [mem_repl_img, function.comp_app] at RC,
    rcases RC with ⟨β, βγ, Re⟩, subst Re,
    exact ⟨_, mul_struct_well_order αord (ord_of_mem_ord γord.ord βγ), rfl⟩,
  have hext : ∀ {R : struct}, struct_to_set R ∈ C → ∀ {S : struct}, struct_to_set S ∈ C → end_extension R S ∨ end_extension S R,
  { simp only [mem_repl_img, function.comp_app], rintros R ⟨β, βγ, Re⟩ S ⟨δ, δγ, Se⟩,
    replace Re := struct_to_set_oto Re, replace Se := struct_to_set_oto Se,
    subst Re, subst Se,
    cases ord_conn' (ord_of_mem_ord γord.ord βγ) (ord_of_mem_ord γord.ord δγ) with βδ βδ,
      left, rotate, right, rename [δ → β, β → δ, δγ → βγ, βγ → δγ], rotate,
      all_goals {
        have βord := ord_of_mem_ord γord.ord βγ, have δord := ord_of_mem_ord γord.ord δγ,
        have sub' : β ⊆ δ, rw ←ord_le_iff_sub βord δord, exact βδ,
        have sub : α.prod β ⊆ α.prod δ := prod_subset_of_subset_of_subset subset_self sub',
        split,
            dsimp [mul_struct], exact sub,
          dsimp [mul_struct, mul_rel], apply rel_sub pair_sep_is_rel,
          intros x y, rw pair_mem_pair_sep, rintros ⟨hx, hy, h⟩,
          rw pair_mem_pair_sep' (sub hx) (sub hy), rw mem_prod at hx hy,
          rcases hx with ⟨a, aα, b, bβ, xab⟩, subst xab,
          rcases hy with ⟨c, cα, d, dβ, ycd⟩, subst ycd,
          simp only [fst_congr, snd_congr] at *,
          rw pair_mem_eps_order' bβ dβ at h,
          rw pair_mem_eps_order' (ord_lt_of_lt_of_le δord bβ βδ) (ord_lt_of_lt_of_le δord dβ βδ),
          exact h,
        dsimp [mul_struct, mul_rel], intros r hr s hs, rw pair_mem_pair_sep' (sub hr) (subset_diff hs),
        simp only [prod_diff, mem_prod, exists_prop, mem_diff] at hr hs,
        rcases hr with ⟨a, aα, b, bβ, rab⟩, subst rab, rcases hs with ⟨c, cα, d, ⟨dδ, dβ⟩, scd⟩, subst scd,
        simp only [fst_congr, snd_congr],
        rw [pair_mem_eps_order' (sub' bβ) dδ, pair_mem_eps_order' aα cα], left,
        rw ←ord_not_le_iff_lt (ord_of_mem_ord δord dδ) (ord_of_mem_ord βord bβ),
        intro db, apply dβ, exact ord_lt_of_le_of_lt βord db bβ, }, },
  have L8M := L8M hC @hext,
  dsimp at L8M, rcases L8M with ⟨well, h₂⟩,
  have h₃ : repl_img (eps_img ∘ set_to_struct) C = repl_img (eps_img ∘ mul_struct α.eps_order_struct ∘ eps_order_struct) γ,
    dsimp [C], rw [repl_img_comp, function.comp.assoc eps_img set_to_struct _],
    have h₃ : ∀ {f : Set → struct}, set_to_struct ∘ struct_to_set ∘ f = f,
      intro f, funext, simp only [function.comp_app, struct_set_struct_eq_self],
    rw h₃,
  rw h₃ at h₂, rw ←h₂,
  have h₄ : mul_struct α.eps_order_struct γ.Union.eps_order_struct = ⟨(repl_img fst C).Union, (repl_img snd C).Union, L8M_lemma hC⟩,
    ext; dsimp [mul_struct],
      have h₄ : ∀ ⦃x : Set⦄, x ∈ repl_img fst C → x.is_rel,
        simp only [mem_repl_img, function.comp_app], rintros P ⟨R, ⟨β, βγ, Re⟩, PR⟩, subst Re, subst PR,
        rw set_fst_eq_fld, dsimp [mul_struct], exact prod_is_rel,
      apply rel_ext prod_is_rel (Union_is_rel h₄),
      simp only [mem_Union, exists_prop, mem_repl_img, function.comp_app, pair_mem_prod], intros a b, split,
        rintro ⟨aα, β, βγ, bβ⟩, refine ⟨_, ⟨_, ⟨_, βγ, rfl⟩, rfl⟩, _⟩,
        rw set_fst_eq_fld, dsimp [mul_struct], rw pair_mem_prod, exact ⟨aα, bβ⟩,
      rintro ⟨P, ⟨R, ⟨β, βγ, Re⟩, PR⟩, abP⟩, subst Re, subst PR,
      rw set_fst_eq_fld at abP, dsimp [mul_struct] at abP, rw pair_mem_prod at abP,
      exact ⟨abP.left, _, βγ, abP.right⟩,
    have h₄ : ∀ ⦃R : Set⦄, R ∈ repl_img snd C → R ⊆ (α.prod γ).prod (α.prod γ),
      intro R, simp only [mem_repl_img, function.comp_app],
      rintro ⟨S, ⟨β, βγ, Se⟩, RS⟩, subst Se, subst RS, rw set_snd_eq_rel,
      dsimp [mul_struct, mul_rel],
      have sub : α.prod β ⊆ α.prod γ, apply prod_subset_of_subset_of_subset subset_self,
        rw ←ord_le_iff_sub (ord_of_mem_ord γord.ord βγ) γord.ord, left, exact βγ,
      exact subset_trans pair_sep_sub_prod (prod_subset_of_subset_of_subset sub sub),
    rw ←limit_ord_eq_Union γord, apply rel_ext' pair_sep_sub_prod (Union_sub h₄),
    intros x hx y hy, simp only [pair_mem_pair_sep' hx hy, mem_Union, exists_prop, mem_repl_img, function.comp_app],
    simp only [mem_prod] at hx hy,
    rcases hx with ⟨a, aα, b, bγ, xab⟩, subst xab,
    rcases hy with ⟨c, cα, d, dγ, ycd⟩, subst ycd,
    have bord := ord_of_mem_ord γord.ord bγ,
    have dord := ord_of_mem_ord γord.ord dγ,
    have hab : a.pair b ∈ α.prod (b.ord_max d).succ,
      rw pair_mem_prod, exact ⟨aα, mem_succ_iff_le.mpr ord_max_le_left⟩,
    have hcd : c.pair d ∈ α.prod (b.ord_max d).succ,
      rw pair_mem_prod, exact ⟨cα, mem_succ_iff_le.mpr (ord_max_le_right bord dord)⟩,
    simp only [fst_congr, snd_congr],
    rw [pair_mem_eps_order bγ dγ, pair_mem_eps_order aα cα], split,
      rintro (bd|⟨bd, ac⟩);
      refine ⟨_, ⟨_, ⟨(b.ord_max d).succ, succ_mem_limit γord (@ord_max_prop (λ x, x ∈ γ) _ bγ _ dγ), rfl⟩, rfl⟩, _⟩;
      rw set_snd_eq_rel; dsimp [mul_struct, mul_rel];
      rw pair_mem_pair_sep' hab hcd; simp only [fst_congr, snd_congr];
      rw [pair_mem_eps_order' (mem_succ_iff_le.mpr ord_max_le_left) (mem_succ_iff_le.mpr (ord_max_le_right bord dord)),
        pair_mem_eps_order' aα cα],
        left, exact bd,
      subst bd, right, exact ⟨rfl, ac⟩,
    rintro ⟨R, ⟨S, ⟨β, βγ, Se⟩, RS⟩, abcd⟩, subst Se, subst RS,
    rw set_snd_eq_rel at abcd, dsimp [mul_struct, mul_rel] at abcd,
    simp only [pair_mem_pair_sep, fst_congr, snd_congr, pair_mem_eps_order' aα cα, eps_order, pair_mem_pair_sep] at abcd,
    rcases abcd with ⟨-, -, (⟨-, -, bd⟩|⟨bd, -, -, ac⟩)⟩,
      left, exact bd,
    right, subst bd, exact ⟨rfl, ac⟩,
  rw [h₄, ord_ot, iso_type_eq_iff_iso], apply eps_img_isomorphic,
  rw [←h₄, ←limit_ord_eq_Union γord], exact mul_struct_well_order αord γord.ord,
  
end

noncomputable def ord_exp_fun (α : Set) : Set → Set := fun f,
  if f.dom = ∅
    then one
  else if ex₁ : ∃ β : Set, β.is_ordinal ∧ f.dom = β.succ
    then (f.fun_value (classical.some ex₁)).ord_mul α
  else if ex₂ : f.dom.limit_ord
    then f.ran.Union
  else ∅

lemma ord_exp_fun_zero {α f : Set} (fdom : f.dom = ∅) : α.ord_exp_fun f = one :=
begin
  rw ord_exp_fun, dsimp, rw if_pos fdom,
end

lemma ord_exp_fun_succ {α f β : Set} (βord : β.is_ordinal) (dom : f.dom = β.succ) :
  α.ord_exp_fun f = (f.fun_value β).ord_mul α :=
begin
  have h : ¬ f.dom = ∅, rw [eq_empty, dom], push_neg, exact ⟨_, self_mem_succ⟩,
  rw ord_exp_fun, dsimp, rw if_neg h,
  have ex₁ : ∃ β : Set, β.is_ordinal ∧ f.dom = β.succ := ⟨_, βord, dom⟩,
  rw dif_pos ex₁,
  obtain ⟨ord, dom'⟩ := classical.some_spec ex₁, rw dom' at dom,
  have h₂ := succ_inj' dom, rw h₂,
end

lemma ord_exp_fun_limit {α f : Set} (fdom : f.dom.limit_ord) :
  α.ord_exp_fun f = f.ran.Union :=
begin
  have ex₀ : ¬ f.dom = ∅, rw dom, exact fdom.ne,
  have ex₁ : ¬ ∃ α : Set, α.is_ordinal ∧ f.dom = α.succ,
    rintro ⟨α, -, γα⟩, exact fdom.ns ⟨_, γα⟩,
  rw ord_exp_fun, dsimp, rw [if_neg ex₀, dif_neg ex₁, if_pos fdom],
end

noncomputable def ord_exp (α β : Set) : Set :=
if α = ∅ then
  if β = ∅ then one else ∅
  else (ord_rec α.ord_exp_fun) β

lemma ord_exp_base_zero {β : Set} (βne : β ≠ ∅) : ord_exp ∅ β = ∅ :=
by rw [ord_exp, if_pos rfl, if_neg βne]

lemma ord_exp_zero {α : Set} : α.ord_exp ∅ = one :=
begin
  by_cases hα : α = ∅,
    rw [ord_exp, if_pos hα, if_pos rfl],
  rw [ord_exp, if_neg hα, ord_rec_spec zero_is_ord, ord_exp_fun_zero (con_fun_dom zero_is_ord)],
end

lemma ord_exp_succ {α β : Set} (βord : β.is_ordinal) : α.ord_exp β.succ = (α.ord_exp β).ord_mul α :=
begin
  by_cases hα : α = ∅,
    rw [ord_exp, if_pos hα, if_neg succ_neq_empty, hα, ord_exp, if_pos rfl],
    by_cases hβ : β = ∅,
      rw [if_pos hβ, ord_mul_zero one_is_ord],
    rw [if_neg hβ, ord_mul_zero zero_is_ord],
  have βord' := succ_ord_of_ord βord,
  rw [ord_exp, if_neg hα, ord_rec_spec βord', ord_exp_fun_succ βord (con_fun_dom βord'), con_fun_spec βord' self_mem_succ,
    ord_exp, if_neg hα],
end

lemma ord_exp_limit {α : Set} (αne : α ≠ ∅) {γ : Set} (γord : γ.limit_ord) : α.ord_exp γ = (repl_img α.ord_exp γ).Union :=
begin
  have dom : (con_fun α.ord_exp_fun γ).dom.limit_ord, rwa con_fun_dom γord.ord,
  rw [ord_exp, if_neg αne, ord_rec_spec γord.ord, ord_exp_fun_limit dom, con_fun_ran_eq γord.ord], congr' 1,
  apply repl_img_ext, intros β βγ, rw [ord_exp, if_neg αne],
end

lemma ord_exp_ord {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  (α.ord_exp β).is_ordinal :=
begin
  revert β, apply trans_ind_schema, intros β βord ind,
  by_cases hβ : β = ∅,
    subst hβ, rw ord_exp_zero, exact one_is_ord,
  by_cases βs : ∃ δ : Set, β = δ.succ,
    rcases βs with ⟨δ, βδ⟩, subst βδ,
    rw ord_exp_succ (ord_of_succ_ord βord),
    exact ord_mul_ord (ind self_mem_succ) αord,
  by_cases hα : α = ∅,
    subst hα, rw ord_exp_base_zero hβ, exact zero_is_ord,
  rw ord_exp_limit hα ⟨βord, hβ, βs⟩, exact Union_ords_is_ord (of_repl_img @ind),
end

theorem ord_one_exp : ∀ {α : Set}, α.is_ordinal → one.ord_exp α = one :=
begin
  apply trans_ind_schema, intros α αord ind,
  by_cases αz : α = ∅,
    subst αz, rw ord_exp_zero,
  by_cases ex : ∃ β : Set, α = β.succ,
    rcases ex with ⟨β, αβ⟩, subst αβ,
    have βord := ord_of_succ_ord αord,
    rw [ord_exp_succ βord, ord_mul_one (ord_exp_ord one_is_ord βord), ind self_mem_succ],
  have αord' : α.limit_ord := ⟨αord, αz, ex⟩,
  rw [ord_exp_limit zero_ne_one.symm αord', eq_iff_subset_and_subset], split,
    apply Union_sub, apply @of_repl_img _ _ (λ x, x ⊆ one), intros β βα,
    have βord := ord_of_mem_ord αord βα,
    rw ←ord_le_iff_sub (ord_exp_ord one_is_ord βord) one_is_ord, right,
    exact ind βα,
  intros z hz, rw [one, succ, union_empty, mem_singleton] at hz, subst hz,
  simp only [mem_Union, exists_prop, mem_repl_img], refine ⟨_, ⟨∅, limit_ord_pos αord', rfl⟩, _⟩,
  rw ord_exp_zero, exact zero_lt_one,
end

theorem nat_ord_add {n : Set} (nω : n ∈ ω) : ∀ {m : Set}, m ∈ ω → n.ord_add m = n + m :=
begin
  have nord := nat_is_ord nω,
  apply induction,
    rw [ord_add_zero nord, add_base nω],
  intros m mω ind, rw [ord_add_succ nord (nat_is_ord mω), add_ind nω mω, ind],
end

theorem nat_ord_mul {n : Set} (nω : n ∈ ω) : ∀ {m : Set}, m ∈ ω → n.ord_mul m = n * m :=
begin
  have nord := nat_is_ord nω,
  apply induction,
    rw [ord_mul_zero nord, mul_base nω],
  intros m mω ind, rw [ord_mul_succ nord (nat_is_ord mω), ind, nat_ord_add (mul_into_nat nω mω) nω, mul_ind nω mω],
end

theorem nat_ord_exp {n : Set} (nω : n ∈ ω) : ∀ {m : Set}, m ∈ ω → n.ord_exp m = n ^ m :=
begin
  have nord := nat_is_ord nω,
  apply induction,
    rw [ord_exp_zero, exp_base nω],
  intros m mω ind, rw [ord_exp_succ (nat_is_ord mω), ind, nat_ord_mul (exp_into_nat nω mω) nω, exp_ind nω mω],
end

theorem two_exp_omega_eq_omega : two.ord_exp ω = ω :=
begin
  rw ord_exp_limit zero_ne_two.symm omega_limit_ord, apply unbounded_Union_eq_nat,
      apply of_repl_img, intros n nω, rw nat_ord_exp two_nat nω, exact exp_into_nat two_nat nω,
    rw mem_repl_img, refine ⟨_, zero_nat, _⟩, rw ord_exp_zero,
  apply of_repl_img, intros n nω, use ord_exp two n.succ,
  have nω' := succ_nat_is_nat nω,
  rw mem_repl_img, refine ⟨⟨_, nω', rfl⟩, _⟩,
  rw [nat_ord_exp two_nat nω, nat_ord_exp two_nat nω'],
  exact exp_lt_of_lt two_nat one_lt_two self_mem_succ nω',
end

-- Theorem 8N (a)
theorem ord_add_normal {α : Set} (αord : α.is_ordinal) : normal α.ord_add :=
begin
  refine norm_of_con (@ord_add_ord _ αord) (@ord_add_limit _ αord) (λ β βord, _),
  rw ord_add_succ αord βord, exact self_mem_succ,
end

-- Theorem 8N (b)
theorem ord_mul_normal {α : Set} (αord : α.is_ordinal) (hα : one ≤ α) : normal α.ord_mul :=
begin
  have αord' := succ_ord_of_ord αord,
  refine norm_of_con (@ord_mul_ord _ αord) (@ord_mul_limit _ αord) (λ β βord, _),
  rw ord_mul_succ αord βord,
  have αβord := ord_mul_ord αord βord,
  nth_rewrite 0 ←ord_add_zero αβord, apply (ord_add_normal αβord).mon αord (ord_lt_of_succ_le zero_is_ord αord hα),
end

lemma exp_positive {α : Set} (αord : α.is_ordinal) (αnz : α ≠ ∅) : ∀ {β : Set}, β.is_ordinal → ∅ ∈ α.ord_exp β :=
begin
  apply trans_ind_schema, intros β βord ind,
  by_cases hβ : β = ∅,
    subst hβ, rw ord_exp_zero, exact zero_lt_one,
  by_cases βs : ∃ δ : Set, β = δ.succ,
    rcases βs with ⟨δ, βδ⟩, subst βδ,
    have δord := ord_of_succ_ord βord,
    have αδord := ord_exp_ord αord δord,
    rw [ord_exp_succ (ord_of_succ_ord βord), ←ord_mul_zero αδord],
    apply (ord_mul_normal αδord (succ_least_upper_bound αδord (ind self_mem_succ))).mon αord,
    exact ord_pos_of_inhab αord (inhabited_of_ne_empty αnz),
  rw ord_exp_limit αnz ⟨βord, hβ, βs⟩,
  simp only [mem_Union, exists_prop, mem_repl_img],
  obtain ⟨δ, δβ⟩ := inhabited_of_ne_empty hβ,
  refine ⟨_, ⟨_, δβ, rfl⟩, ind δβ⟩,
end

-- Theorem 8N (c)
theorem ord_exp_normal {α : Set} (αord : α.is_ordinal) (hα : two ≤ α) : normal α.ord_exp :=
begin
  have αnz : α ≠ ∅, intro αz, subst αz, cases hα,
      exact mem_empty _ hα,
    exact zero_ne_two.symm hα,
  refine norm_of_con (@ord_exp_ord _ αord) (@ord_exp_limit _ αnz) (λ β βord, _),
  have αβord := ord_exp_ord αord βord,
  rw ord_exp_succ βord, nth_rewrite 0 ←ord_mul_one αβord,
  apply (ord_mul_normal αβord (succ_least_upper_bound αβord (exp_positive αord αnz βord))).mon αord,
  apply ord_lt_of_succ_le one_is_ord αord hα,
end

-- Corollary 8P (a)
theorem ord_add_lt_iff {α : Set} (αord : α.is_ordinal) :
∀ {β : Set}, β.is_ordinal → ∀ {γ : Set}, γ.is_ordinal → (β ∈ γ ↔ α.ord_add β ∈ α.ord_add γ) :=
@mon_op_mon_iff _ (@ord_add_ord _ αord) (@ord_add_normal _ αord).mon

theorem ord_mul_lt_iff {α : Set} (αord : α.is_ordinal) (hα : one ≤ α) :
∀ {β : Set}, β.is_ordinal → ∀ {γ : Set}, γ.is_ordinal → (β ∈ γ ↔ α.ord_mul β ∈ α.ord_mul γ) :=
@mon_op_mon_iff _ (@ord_mul_ord _ αord) (@ord_mul_normal _ αord hα).mon

theorem ord_exp_lt_iff {α : Set} (αord : α.is_ordinal) (hα : two ≤ α) :
∀ {β : Set}, β.is_ordinal → ∀ {γ : Set}, γ.is_ordinal → (β ∈ γ ↔ α.ord_exp β ∈ α.ord_exp γ) :=
@mon_op_mon_iff _ (@ord_exp_ord _ αord) (@ord_exp_normal _ αord hα).mon

theorem ord_add_le_iff {α : Set} (αord : α.is_ordinal) :
∀ {β : Set}, β.is_ordinal → ∀ {γ : Set}, γ.is_ordinal → (β ≤ γ ↔ α.ord_add β ≤ α.ord_add γ) :=
@mon_op_le_iff _ (@ord_add_ord _ αord) (@ord_add_normal _ αord).mon

theorem ord_mul_le_iff {α : Set} (αord : α.is_ordinal) (hα : one ≤ α) :
∀ {β : Set}, β.is_ordinal → ∀ {γ : Set}, γ.is_ordinal → (β ≤ γ ↔ α.ord_mul β ≤ α.ord_mul γ) :=
@mon_op_le_iff _ (@ord_mul_ord _ αord) (@ord_mul_normal _ αord hα).mon

theorem ord_exp_le_iff {α : Set} (αord : α.is_ordinal) (hα : two ≤ α) :
∀ {β : Set}, β.is_ordinal → ∀ {γ : Set}, γ.is_ordinal → (β ≤ γ ↔ α.ord_exp β ≤ α.ord_exp γ) :=
@mon_op_le_iff _ (@ord_exp_ord _ αord) (@ord_exp_normal _ αord hα).mon

-- Corollary 8P (b)
theorem ord_add_cancel {α : Set} (αord : α.is_ordinal) :
  ∀ {β : Set}, β.is_ordinal → ∀ {γ : Set}, γ.is_ordinal → α.ord_add β = α.ord_add γ → β = γ :=
@mon_op_inj _ (@ord_add_ord _ αord) (@ord_add_normal _ αord).mon

theorem ord_mul_cancel {α : Set} (αord : α.is_ordinal) (hα : one ≤ α) :
  ∀ {β : Set}, β.is_ordinal → ∀ {γ : Set}, γ.is_ordinal → α.ord_mul β = α.ord_mul γ → β = γ :=
@mon_op_inj _ (@ord_mul_ord _ αord) (@ord_mul_normal _ αord hα).mon

theorem ord_exp_cancel {α : Set} (αord : α.is_ordinal) (hα : two ≤ α) :
  ∀ {β : Set}, β.is_ordinal → ∀ {γ : Set}, γ.is_ordinal → α.ord_exp β = α.ord_exp γ → β = γ :=
@mon_op_inj _ (@ord_exp_ord _ αord) (@ord_exp_normal _ αord hα).mon

-- Theorem 8Q
theorem ord_add_le_right {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) (αβ : α ≤ β) :
  ∀ {γ : Set}, γ.is_ordinal → α.ord_add γ ≤ β.ord_add γ :=
begin
  apply trans_ind_schema, intros γ γord ind,
  by_cases γe : γ = ∅,
    subst γe, rwa [ord_add_zero αord, ord_add_zero βord],
  by_cases ex : ∃ δ : Set, γ = δ.succ,
    rcases ex with ⟨δ, γδ⟩, subst γδ,
    have δord := ord_of_succ_ord γord,
    rw [ord_add_succ αord δord, ord_add_succ βord δord, ←ord_succ_le_iff (ord_add_ord αord δord) (ord_add_ord βord δord)],
    exact ind self_mem_succ,
  have γord' : γ.limit_ord := ⟨γord, γe, ex⟩,
  rw [ord_le_iff_sub (ord_add_ord αord γord) (ord_add_ord βord γord), ord_add_limit αord γord', ord_add_limit βord γord'],
  simp only [subset_def, mem_Union, exists_prop, mem_repl_img],
  rintro μ ⟨αδ, ⟨δ, δγ, αδαδ⟩, μαδ⟩, subst αδαδ, refine ⟨_, ⟨_, δγ, rfl⟩, _⟩,
  exact ord_lt_of_lt_of_le (ord_add_ord βord (ord_of_mem_ord γord δγ)) μαδ (ind δγ),
end

theorem ord_mul_le_right {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) (αβ : α ≤ β) :
  ∀ {γ : Set}, γ.is_ordinal → α.ord_mul γ ≤ β.ord_mul γ :=
begin
  apply trans_ind_schema, intros γ γord ind,
  by_cases γe : γ = ∅,
    subst γe, rw [ord_mul_zero αord, ord_mul_zero βord], exact le_self,
  by_cases ex : ∃ δ : Set, γ = δ.succ,
    rcases ex with ⟨δ, γδ⟩, subst γδ,
    have δord := ord_of_succ_ord γord,
    rw [ord_mul_succ αord δord, ord_mul_succ βord δord],
    have βδord := ord_mul_ord βord δord,
    apply ord_le_trans (ord_add_ord βδord βord) (ord_add_le_right (ord_mul_ord αord δord) βδord (ind self_mem_succ) αord),
    rwa ←ord_add_le_iff βδord αord βord,
  have γord' : γ.limit_ord := ⟨γord, γe, ex⟩,
  rw [ord_le_iff_sub (ord_mul_ord αord γord) (ord_mul_ord βord γord), ord_mul_limit αord γord', ord_mul_limit βord γord'],
  simp only [subset_def, mem_Union, exists_prop, mem_repl_img],
  rintro μ ⟨αδ, ⟨δ, δγ, αδαδ⟩, μαδ⟩, subst αδαδ, refine ⟨_, ⟨_, δγ, rfl⟩, _⟩,
  exact ord_lt_of_lt_of_le (ord_mul_ord βord (ord_of_mem_ord γord δγ)) μαδ (ind δγ),
end

theorem ord_exp_le_right {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) (αβ : α ≤ β) :
  ∀ {γ : Set}, γ.is_ordinal → α.ord_exp γ ≤ β.ord_exp γ :=
begin
  apply trans_ind_schema, intros γ γord ind,
  by_cases γe : γ = ∅,
    subst γe, rw [ord_exp_zero, ord_exp_zero], exact le_self,
  by_cases ex : ∃ δ : Set, γ = δ.succ,
    rcases ex with ⟨δ, γδ⟩, subst γδ,
    have δord := ord_of_succ_ord γord,
    rw [ord_exp_succ δord, ord_exp_succ δord],
    have βδord := ord_exp_ord βord δord,
    apply ord_le_trans (ord_mul_ord βδord βord) (ord_mul_le_right (ord_exp_ord αord δord) βδord (ind self_mem_succ) αord),
    by_cases δz : δ = ∅,
      subst δz, rwa [ord_exp_zero, ord_one_mul αord, ord_one_mul βord],
    by_cases βz : β = ∅,
      subst βz, rw [ord_exp_base_zero δz, ord_zero_mul αord, ord_zero_mul βord], exact le_self,
    rwa ←ord_mul_le_iff βδord (succ_least_upper_bound βδord (exp_positive βord βz δord)) αord βord,
  have γord' : γ.limit_ord := ⟨γord, γe, ex⟩,
  by_cases αz : α = ∅,
    subst αz, rw [ord_exp_base_zero γe], exact empty_le_ord (ord_exp_ord βord γord),
  have βγord := ord_exp_ord βord γord,
  rw [ord_le_iff_sub (ord_exp_ord αord γord) βγord, ord_exp_limit αz γord'],
  apply Union_sub, apply @of_repl_img _ _ (λ x, x ⊆ β.ord_exp γ), intros δ δγ,
  have δord := ord_of_mem_ord γord δγ,
  rw ←ord_le_iff_sub (ord_exp_ord αord δord) βγord, apply ord_le_trans βγord (ind δγ),
  cases empty_le_ord βord with hβ hβ,
    replace hβ := succ_least_upper_bound βord hβ, change one ≤ β at hβ,
    cases hβ with hβ hβ,
      replace hβ := succ_least_upper_bound βord hβ, change two ≤ β at hβ,
      rw ←ord_exp_le_iff βord hβ δord γord, exact or.inl δγ,
    subst hβ, rw [ord_one_exp δord, ord_one_exp γord], exact le_self,
  subst hβ, exfalso, exact αz (ord_eq_zero_of_le_zero αord αβ),
end

theorem ord_sub_theorem {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) (αβ : α ≤ β) :
  ∃! δ : Set, δ.is_ordinal ∧ α.ord_add δ = β :=
begin
  refine exists_unique_of_exists_of_unique _ (λ δ γ hδ hγ, ord_add_cancel αord hδ.left hγ.left (by rw [hδ.right, hγ.right])),
  have αβ' : α.ord_add ∅ ≤ β, rwa ord_add_zero αord,
  obtain ⟨δ, δord, δβ, un⟩ := exists_large_ord_of_norm (@ord_add_ord _ αord) (@ord_add_normal _ αord) βord αβ',
  dsimp at δβ un, cases δβ,
    exfalso, specialize un (succ_ord_of_ord δord), rw ord_add_succ αord δord at un,
    specialize un (succ_least_upper_bound βord δβ),
    exact succ_ord_not_le_self δord un,
  exact ⟨_, δord, δβ⟩,
end

theorem ord_div_theorem {α : Set} (αord : α.is_ordinal) {δ : Set} (δord : δ.is_ordinal) (δnz : δ ≠ ∅) :
  ∃! β : Set, β.is_ordinal ∧ ∃! γ : Set, γ.is_ordinal ∧ α = (δ.ord_mul β).ord_add γ ∧ γ ∈ δ :=
begin
  refine exists_unique_of_exists_of_unique _ _,
    have hδ : one ≤ δ := succ_least_upper_bound δord (ord_pos_of_inhab δord (inhabited_of_ne_empty δnz)),
    have δα : δ.ord_mul ∅ ≤ α, rw ord_mul_zero δord, exact empty_le_ord αord,
    obtain ⟨β, βord, δβα, h⟩ := exists_large_ord_of_norm (@ord_mul_ord _ δord) (@ord_mul_normal _ δord hδ) αord δα,
    have δβord := ord_mul_ord δord βord,
    dsimp at δβα h, obtain ⟨γ, ⟨γord, h'⟩, h''⟩ := ord_sub_theorem δβord αord δβα,
    refine ⟨_, βord, _, ⟨γord, h'.symm, _⟩, _⟩,
      rw ←ord_not_le_iff_lt δord γord, intro δγ,
      refine succ_ord_not_le_self βord (h (succ_ord_of_ord βord) _),
      rwa [ord_mul_succ δord βord, ←h', ←ord_add_le_iff δβord δord γord],
    dsimp, rintros γ' ⟨γord', h''', γδ'⟩, apply ord_add_cancel δβord γord' γord, rw [h', ←h'''],
  rintros β₁ β₂ ⟨βord₁, γ₁, ⟨γord₁, h₁, γδ₁⟩, -⟩ ⟨βord₂, γ₂, ⟨γord₂, h₂, γδ₂⟩, -⟩,
  apply ord_eq_of_not_lt βord₁ βord₂,
  rotate, rename [β₁ → β₂, β₂ → β₁, βord₁ → βord₂, βord₂ → βord₁, γ₁ → γ₂, γ₂ → γ₁, h₁ → h₂, h₂ → h₁, γord₁ → γord₂,
    γord₂ → γord₁, γδ₁ → γδ₂, γδ₂ → γδ₁],
  all_goals { 
    intro ββ, apply ord_mem_irrefl αord, nth_rewrite 0 h₁, rw h₂,
    have h' := ord_mul_ord δord βord₂,
    have h := ord_add_ord h' γord₂,
    apply @ord_lt_of_lt_of_le _ ((δ.ord_mul β₁).ord_add δ) _ h,
      rwa ←ord_add_lt_iff (ord_mul_ord δord βord₁) γord₁ δord,
    rw ←ord_mul_succ δord βord₁, apply @ord_le_trans _ (δ.ord_mul β₂) _ h,
      rw ←ord_mul_le_iff δord (succ_least_upper_bound δord (ord_pos_of_inhab δord (inhabited_of_ne_empty δnz)))
        (succ_ord_of_ord βord₁) βord₂,
      exact succ_least_upper_bound βord₂ ββ,
    nth_rewrite 0 ←ord_add_zero h',
    rw ←ord_add_le_iff h' zero_is_ord γord₂, exact empty_le_ord γord₂, },
end

theorem ord_log_theorem {α : Set} (αord : α.is_ordinal) (αnz : α ≠ ∅)
  {β : Set} (βord : β.is_ordinal) (hβ : two ≤ β) :
  ∃! γ : Set, γ.is_ordinal ∧ ∃! δ : Set, δ.is_ordinal ∧ ∃! ρ : Set, ρ.is_ordinal ∧
  α = ((β.ord_exp γ).ord_mul δ).ord_add ρ ∧ δ ≠ ∅ ∧ δ ∈ β ∧ ρ ∈ β.ord_exp γ :=
begin
  have βnz : β ≠ ∅ := not_zero_of_pos (ord_lt_of_lt_of_le βord zero_lt_two hβ),
  refine exists_unique_of_exists_of_unique _ _,
    have βα : β.ord_exp ∅ ≤ α, rw ord_exp_zero,
      exact succ_least_upper_bound αord (ord_pos_of_inhab αord (inhabited_of_ne_empty αnz)),
    obtain ⟨γ, γord, βγα, un⟩ := exists_large_ord_of_norm (@ord_exp_ord _ βord) (@ord_exp_normal _ βord hβ) αord βα,
    have h'' : β.ord_exp γ ≠ ∅ := not_zero_of_pos (exp_positive βord βnz γord),
    obtain ⟨δ, ⟨δord, ρ, ⟨ρord, αe, hρ⟩, h⟩, h'⟩ := ord_div_theorem αord (ord_exp_ord βord γord) h'',
    dsimp at *,
    have δnz : δ ≠ ∅, intro δz, subst δz,
      rw [ord_mul_zero (ord_exp_ord βord γord), ord_zero_add ρord] at αe, subst αe,
      exact ord_mem_irrefl αord (ord_lt_of_lt_of_le αord hρ βγα),
    have δβ : δ ∈ β, rw ←ord_not_le_iff_lt βord δord, intro βδ,
      apply succ_ord_not_le_self γord, apply un (succ_ord_of_ord γord),
      apply @ord_le_trans _ ((β.ord_exp γ).ord_mul δ) _ αord,
        have h''' : one ≤ β.ord_exp γ := succ_least_upper_bound (ord_exp_ord βord γord)
          (ord_pos_of_inhab (ord_exp_ord βord γord) (inhabited_of_ne_empty h'')),
        rwa [ord_exp_succ γord, ←ord_mul_le_iff (ord_exp_ord βord γord) h''' βord δord],
      rw [←ord_add_zero (ord_mul_ord (ord_exp_ord βord γord) δord), αe,
        ←ord_add_le_iff (ord_mul_ord (ord_exp_ord βord γord) δord) zero_is_ord ρord],
      exact empty_le_ord ρord,
    refine ⟨_, γord, _, ⟨δord, _, ⟨ρord, αe, δnz, δβ, hρ⟩, _⟩, _⟩; dsimp,
      rintros ρ' ⟨ρord', αe', -, -, hρ'⟩, exact h _ ⟨ρord', αe', hρ'⟩,
    rintros δ' ⟨δord', ρ', ⟨ρord', αe', δnz', δβ', hρ'⟩, h'''⟩, dsimp at h''',
    apply h' _ ⟨δord', _, ⟨ρord', αe', hρ'⟩, _⟩, dsimp,
    rintros ρ'' ⟨ρord'', αe'', hρ''⟩, exact h''' _ ⟨ρord'', αe'', δnz', δβ', hρ''⟩,
  rintros γ₁ γ₂ ⟨γord₁, δ₁, ⟨δord₁, ρ₁, ⟨ρord₁, αe₁, δnz₁, δβ₁, hρ₁⟩, -⟩, -⟩
    ⟨γord₂, δ₂, ⟨δord₂, ρ₂, ⟨ρord₂, αe₂, δnz₂, δβ₂, hρ₂⟩, -⟩, -⟩,
  apply ord_eq_of_not_lt γord₁ γord₂, rotate,
  rename [γ₁ → γ₂, γord₁ → γord₂, δ₁ → δ₂, δord₁ → δord₂, ρ₁ → ρ₂, ρord₁ → ρord₂, αe₁ → αe₂, δnz₁ → δnz₂, δβ₁ → δβ₂, hρ₁ → hρ₂,
    γ₂ → γ₁, γord₂ → γord₁, δ₂ → δ₁, δord₂ → δord₁, ρ₂ → ρ₁, ρord₂ → ρord₁, αe₂ → αe₁, δnz₂ → δnz₁, δβ₂ → δβ₁, hρ₂ → hρ₁],
  all_goals {
    intro γγ, apply ord_mem_irrefl αord, nth_rewrite 0 αe₁, subst αe₂,
    apply @ord_lt_of_lt_of_le _ (((β.ord_exp γ₁).ord_mul δ₁).ord_add (β.ord_exp γ₁)) _ αord,
      rwa ←ord_add_lt_iff (ord_mul_ord (ord_exp_ord βord γord₁) δord₁) ρord₁ (ord_exp_ord βord γord₁),
    apply @ord_le_trans _ ((β.ord_exp γ₁).ord_mul β) _ αord,
      have δβ' := succ_least_upper_bound βord δβ₁,
      have h : one ≤ β.ord_exp γ₁ := succ_least_upper_bound (ord_exp_ord βord γord₁) (exp_positive βord βnz γord₁),
      rwa [←ord_mul_succ (ord_exp_ord βord γord₁) δord₁, ←ord_mul_le_iff (ord_exp_ord βord γord₁) h (succ_ord_of_ord δord₁) βord],
    apply @ord_le_trans _ (β.ord_exp γ₂) _ αord,
      rw [←ord_exp_succ γord₁, ←ord_exp_le_iff βord hβ (succ_ord_of_ord γord₁) γord₂],
      exact succ_least_upper_bound γord₂ γγ,
    apply @ord_le_trans _ ((β.ord_exp γ₂).ord_mul δ₂) _ αord,
      have h' : one ≤ β.ord_exp γ₂ := succ_least_upper_bound (ord_exp_ord βord γord₂) (exp_positive βord βnz γord₂),
      nth_rewrite 0 ←ord_mul_one (ord_exp_ord βord γord₂),
      rw ←ord_mul_le_iff (ord_exp_ord βord γord₂) h' one_is_ord δord₂,
      exact succ_least_upper_bound δord₂ (ord_pos_of_inhab δord₂ (inhabited_of_ne_empty δnz₂)),
    nth_rewrite 0 ←ord_add_zero (ord_mul_ord (ord_exp_ord βord γord₂) δord₂),
    rw ←ord_add_le_iff (ord_mul_ord (ord_exp_ord βord γord₂) δord₂) zero_is_ord ρord₂,
    exact empty_le_ord ρord₂, },
end

lemma right_addend_zero_of_add_zero {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal)
  (h : α.ord_add β = ∅) : β = ∅ :=
begin
  apply classical.by_contradiction, intro hβ,
  have h' : one ≤ β := succ_least_upper_bound βord (ord_pos_of_inhab βord (inhabited_of_ne_empty hβ)),
  refine mem_empty ∅ (ord_lt_of_lt_of_le zero_is_ord (zero_mem_succ_ord αord) _),
  rwa [←ord_add_one_eq_succ αord, ←h, ←ord_add_le_iff αord one_is_ord βord],
end

lemma add_not_zero_of_right_not_zero {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal)
  (h : β ≠ ∅) : α.ord_add β ≠ ∅ :=
λ h', h (right_addend_zero_of_add_zero αord βord h')

-- Theorem 8R
theorem ord_exp_add {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal)
  {γ : Set} (γord : γ.is_ordinal) : α.ord_exp (β.ord_add γ) = (α.ord_exp β).ord_mul (α.ord_exp γ) :=
begin
  cases empty_le_ord αord with hα hα,
    replace hα := succ_least_upper_bound αord hα, cases hα,
      replace hα := succ_least_upper_bound αord hα, change two ≤ α at hα,
      have αnz : α ≠ ∅ := not_zero_of_pos (ord_lt_of_lt_of_le αord zero_lt_two hα),
      revert γ, apply trans_ind_schema, intros γ γord ind,
      rcases ord_cases γord with (γz|(⟨δ, γδ⟩|γord')),
      { subst γz, rw [ord_add_zero βord, ord_exp_zero, ord_mul_one (ord_exp_ord αord βord)], },
      { subst γδ, have δord := ord_of_succ_ord γord,
        rw [ord_add_succ βord δord, ord_exp_succ (ord_add_ord βord δord), ind self_mem_succ,
          ord_mul_assoc (ord_exp_ord αord βord) (ord_exp_ord αord δord) αord, ←ord_exp_succ δord], },
      { rw [ord_add_limit βord γord', ord_exp_limit αnz γord'],
        have Sne : repl_img β.ord_add γ ≠ ∅, apply ne_empty_of_inhabited, use β,
          rw mem_repl_img, refine ⟨_, limit_ord_pos γord', _⟩, rw ord_add_zero βord,
        have Sord : ∀ ⦃δ : Set⦄, δ ∈ repl_img β.ord_add γ → δ.is_ordinal, intro δ, rw mem_repl_img,
          rintro ⟨ρ, ργ, δe⟩, subst δe, exact ord_add_ord βord (ord_of_mem_ord γord ργ),
        have h := sup_norm_fun (@ord_exp_ord _ αord) (@ord_exp_normal _ αord hα) Sne Sord,
        have Tne : repl_img α.ord_exp γ ≠ ∅, apply ne_empty_of_inhabited, use one,
          rw mem_repl_img, refine ⟨_, limit_ord_pos γord', _⟩, rw ord_exp_zero,
        have Tord : ∀ ⦃δ : Set⦄, δ ∈ repl_img α.ord_exp γ → δ.is_ordinal, intro δ, rw mem_repl_img,
          rintro ⟨ρ, ργ, δe⟩, subst δe, exact ord_exp_ord αord (ord_of_mem_ord γord ργ),
        have αβord := ord_exp_ord αord βord,
        have hαβ : one ≤ α.ord_exp β := succ_least_upper_bound αβord (exp_positive αord αnz βord),
        have h' := sup_norm_fun (@ord_mul_ord _ αβord) (@ord_mul_normal _ αβord hαβ) Tne Tord,
        dsimp at h h',
        rw [←sup, ←sup, h, h', repl_img_comp, repl_img_comp], congr' 1, apply repl_img_ext,
        intros δ δγ, simp only [function.comp_app], rw ind δγ, },
    change one = α at hα, subst hα,
    rw [ord_one_exp (ord_add_ord βord γord), ord_one_exp βord, ord_one_exp γord, ord_mul_one one_is_ord],
  subst hα, by_cases hγ : γ = ∅,
    subst hγ, by_cases hβ : β = ∅,
      subst hβ, simp only [ord_add_zero zero_is_ord, ord_exp_zero, ord_mul_one one_is_ord],
    rw [ord_add_zero βord, ord_exp_zero, ord_exp_base_zero hβ, ord_mul_one zero_is_ord],
  have h := add_not_zero_of_right_not_zero βord γord hγ,
  rw [ord_exp_base_zero h, ord_exp_base_zero hγ, ord_mul_zero (ord_exp_ord zero_is_ord βord)],
end

theorem ord_mul_eq_zero {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  α.ord_mul β = ∅ ↔ α = ∅ ∨ β = ∅ :=
⟨λ h, classical.by_contradiction (λ h', begin
  push_neg at h', rcases h' with ⟨hα, hβ⟩,
  replace hα := succ_least_upper_bound αord (ord_pos_of_inhab αord (inhabited_of_ne_empty hα)),
  replace hβ := succ_least_upper_bound βord (ord_pos_of_inhab βord (inhabited_of_ne_empty hβ)),
  refine mem_empty ∅ (ord_lt_of_succ_le zero_is_ord zero_is_ord (@ord_le_trans _ (α.ord_mul one) _ zero_is_ord _ _)),
    change one ≤ α.ord_mul one, nth_rewrite 0 ←ord_mul_one one_is_ord, apply ord_mul_le_right one_is_ord αord hα one_is_ord,
  rwa [←h, ←ord_mul_le_iff αord hα one_is_ord βord],
end), λ h, or.elim h (λ h', by rw [h', ord_zero_mul βord]) (λ h', by rw [h', ord_mul_zero αord])⟩

-- Theorem 8S
theorem ord_exp_exp {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal)
  {γ : Set} (γord : γ.is_ordinal) : (α.ord_exp β).ord_exp γ = α.ord_exp (β.ord_mul γ) :=
begin
  cases empty_le_ord αord with hα hα,
    replace hα := succ_least_upper_bound αord hα, cases hα,
      replace hα := succ_least_upper_bound αord hα, change two ≤ α at hα,
      have αnz : α ≠ ∅ := not_zero_of_pos (ord_lt_of_lt_of_le αord zero_lt_two hα),
      have αβnz : α.ord_exp β ≠ ∅ := not_zero_of_pos (exp_positive αord αnz βord),
      revert γ, apply trans_ind_schema, intros γ γord ind,
      rcases ord_cases γord with (γz|(⟨δ, γδ⟩|γord')),
      { subst γz, simp only [ord_exp_zero, ord_mul_zero βord], },
      { subst γδ, have δord := ord_of_succ_ord γord,
        rw [ord_exp_succ δord, ind self_mem_succ, ←ord_exp_add αord (ord_mul_ord βord δord) βord,
          ←ord_mul_succ βord δord], },
      { rw [ord_mul_limit βord γord', ←sup],
        have Sne : repl_img β.ord_mul γ ≠ ∅, apply ne_empty_of_inhabited, use ∅,
          rw mem_repl_img, refine ⟨_, limit_ord_pos γord', _⟩, rw ord_mul_zero βord,
        have Sord : ∀ ⦃δ : Set⦄, δ ∈ repl_img β.ord_mul γ → δ.is_ordinal,
          apply of_repl_img, intros δ δγ, exact ord_mul_ord βord (ord_of_mem_ord γord δγ),
        have h := sup_norm_fun (@ord_exp_ord _ αord) (@ord_exp_normal _ αord hα) Sne Sord, dsimp at h,
        rw [h, ord_exp_limit αβnz γord', sup, repl_img_comp], congr' 1, apply repl_img_ext,
        intros δ δγ, rw [function.comp_app, ind δγ], },
    change one = α at hα, subst hα,
    rw [ord_one_exp βord, ord_one_exp (ord_mul_ord βord γord), ord_one_exp γord],
  subst hα, by_cases βγ : β.ord_mul γ = ∅,
    rw [βγ, ord_exp_zero], rw ord_mul_eq_zero βord γord at βγ, cases βγ with hβ hγ,
      rw [hβ, ord_exp_zero, ord_one_exp γord],
    rw [hγ, ord_exp_zero],
  rw ord_exp_base_zero βγ, rw ord_mul_eq_zero βord γord at βγ, push_neg at βγ,
  rw [ord_exp_base_zero βγ.left, ord_exp_base_zero βγ.right],
end

lemma ord_finite {α : Set} (αord : α.is_ordinal) : α.is_finite ↔ α ∈ ω :=
begin
  split,
    intro αfin, rw [←ord_not_le_iff_lt omega_is_ord αord, ord_le_iff_sub omega_is_ord αord], intro ωα,
    exact nat_infinite (subset_finite_of_finite αfin ωα),
  exact nat_finite,
end

-- revisiting countable sets

lemma nat_countable {n : Set} (nω : n ∈ ω) : n.countable :=
countable_iff.mpr (or.inl ((ord_finite (nat_is_ord nω)).mpr nω))

lemma omega_countable : countable ω :=
dominates_self

lemma sub_dom_of_dom {A B : Set} (AB : A ⊆ B) {C : Set} (BC : B ≼ C) : A ≼ C :=
begin
  rcases BC with ⟨f, fBC, foto⟩,
  refine ⟨f.restrict A, restrict_into_fun fBC AB, restrict_one_to_one fBC.left foto _⟩,
  rw fBC.right.left, exact AB,
end

lemma sub_countable {A B : Set} (AB : A ⊆ B) (hB : B.countable) : A.countable :=
sub_dom_of_dom AB hB

theorem prod_countable {A : Set} (hA : A.countable) {B : Set} (hB : B.countable) : (A.prod B).countable :=
begin
  rw ←countable_card at *,
  apply @card_le_trans _ (B.card.card_mul (card ω)) (mul_cardinal ⟨_, rfl⟩ ⟨_, rfl⟩),
    rw [card_mul_comm ⟨_, rfl⟩ ⟨_, rfl⟩, card_mul_spec rfl rfl],
    exact card_mul_le_of_le_left ⟨_, rfl⟩ ⟨_, rfl⟩ hA ⟨_, rfl⟩,
  nth_rewrite 1 ←aleph_mul_aleph_eq_aleph,
  exact card_mul_le_of_le_left ⟨_, rfl⟩ ⟨_, rfl⟩ hB ⟨_, rfl⟩,
end

lemma countable_iff_onto {A : Set} (Ain : A.inhab) : A.countable ↔ ∃ f : Set, f.onto_fun ω A :=
by rw [countable, dominated_iff_exists_onto_fun Ain]

-- Theorem 6Q
theorem Union_countable : ∀ {A : Set}, A.countable → (∀ ⦃B : Set⦄, B ∈ A → B.countable) → A.Union.countable :=
begin
  have h₁ : ∀ {A : Set}, ∅ ∉ A → A.countable → (∀ {B : Set}, B ∈ A → B.countable) → A.Union.countable,
    intros A h₁ Ac hA,
    by_cases Ain : A.inhab,
      rw countable_iff_onto Ain at Ac, rcases Ac with ⟨G, Gonto⟩,
      let H := pair_sep_eq ω (into_funs ω A.Union).powerset (λ m, {g ∈ into_funs ω (G.fun_value m) | g.onto_fun ω (G.fun_value m)}),
      have Hfun : H.is_function := pair_sep_eq_is_fun,
      have Hdom : H.dom = ω, apply pair_sep_eq_dom_eq, dsimp, intros n nω, rw mem_powerset,
        intros g hg, rw mem_sep at hg, rw mem_into_funs, refine into_of_into_ran_sub _ (into_of_onto hg.right),
        apply subset_Union_of_mem, rw ←Gonto.right.right, apply fun_value_def'' Gonto.left,
        rw Gonto.right.left, exact nω,
      have hH : ∀ m : Set, m ∈ ω → H.fun_value m ≠ ∅, intros m mω,
        rw ←Hdom at mω, rw pair_sep_eq_fun_value mω, dsimp, apply ne_empty_of_inhabited,
        have GmA : G.fun_value m ∈ A, rw ←Gonto.right.right, apply fun_value_def'' Gonto.left,
          rw [Gonto.right.left, ←Hdom], exact mω,
        have Gmne : G.fun_value m ≠ ∅, intro Gme, rw Gme at GmA, exact h₁ GmA,
        specialize hA GmA, rw countable_iff_onto (inhabited_of_ne_empty Gmne) at hA,
        rcases hA with ⟨g, gonto⟩, use g, rw [mem_sep, mem_into_funs],
        exact ⟨into_of_onto gonto, gonto⟩,
      have memHm : ∀ {m : Set}, m ∈ ω → ∀ {g : Set}, g ∈ H.fun_value m ↔ g.onto_fun ω (G.fun_value m),
        intros m mω g, rw ←Hdom at mω, rw pair_sep_eq_fun_value mω, dsimp, rw [mem_sep, mem_into_funs], split,
          rintro ⟨-, h⟩, exact h,
        intro h, exact ⟨into_of_onto h, h⟩,
      obtain ⟨F, Ffun, Fdom, hF⟩ := ax_ch_2 ⟨Hfun, Hdom, hH⟩,
      let f := pair_sep_eq (prod ω ω) A.Union (λ z, (F.fun_value z.fst).fun_value z.snd),
      have fonto : f.onto_fun (prod ω ω) A.Union, refine ⟨pair_sep_eq_is_fun, pair_sep_eq_dom_eq _, pair_sep_eq_ran_eq _⟩; dsimp,
          simp only [mem_prod, mem_Union, exists_prop], rintros z ⟨m, mω, n, nω, zmn⟩, subst zmn, rw [fst_congr, snd_congr],
          have h := (memHm mω).mp (hF _ mω),
          use G.fun_value m, split,
            rw ←Gonto.right.right, apply fun_value_def'' Gonto.left, rw Gonto.right.left, exact mω,
          rw ←h.right.right, apply fun_value_def'' h.left, rw h.right.left, exact nω,
        simp only [mem_Union, exists_prop], rintros y ⟨B, BA, yB⟩,
        rw [←Gonto.right.right, mem_ran_iff Gonto.left] at BA, rcases BA with ⟨m, mω, BGm⟩, subst BGm,
        rw Gonto.right.left at mω, specialize hF _ mω, rw memHm mω at hF,
        rw [←hF.right.right, mem_ran_iff hF.left] at yB, rcases yB with ⟨n, nω, xe⟩, subst xe,
        rw hF.right.left at nω, use m.pair n, simp only [pair_mem_prod, fst_congr, snd_congr],
        exact ⟨⟨mω, nω⟩, rfl⟩,
      have Ain' : A.Union.inhab, rcases Ain with ⟨B, BA⟩,
        have Bin : B.inhab := classical.by_contradiction (λ Bnin,
          have Bne : B = ∅ := classical.by_contradiction (λ Bne, Bnin (inhabited_of_ne_empty Bne)),
          h₁ (Bne ▸ BA)),
        rcases Bin with ⟨x, xB⟩, use x, rw mem_Union, exact ⟨_, BA, xB⟩,
      rw countable_iff_onto Ain', obtain ⟨f', fonto', foto'⟩ := nat_prod_nat_equin_nat,
      use f.comp f'.inv, refine ⟨T3H_a fonto.left (T3F_a.mpr foto'), _, _⟩,
          have h : f'.inv.ran ⊆ f.dom, rw [T3E_b, fonto'.right.left, fonto.right.left], exact subset_self,
          rw [dom_comp h, T3E_a, fonto'.right.right],
        have h : f.dom ⊆ f'.inv.ran, rw [T3E_b, fonto'.right.left, fonto.right.left], exact subset_self,
        rw [ran_comp h, fonto.right.right],
    have h : A = ∅ := classical.by_contradiction (λ Ane, Ain (inhabited_of_ne_empty Ane)),
    subst h, rw union_empty_eq_empty, exact nat_countable zero_nat,
  intros A Ac hA, rw Union_diff_empty_eq,
  refine h₁ _ (sub_countable subset_diff Ac) _,
    intro h, rw [mem_diff, mem_singleton] at h, exact h.right rfl,
  intros B hB, rw [mem_diff, mem_singleton] at hB, exact hA hB.left,
end

theorem union_countable {A : Set} (Ac : A.countable) {B : Set} (Bc : B.countable) : (A ∪ B).countable :=
begin
  rw union_eq_Union, apply Union_countable, rw ←countable_card,
    by_cases h : A ∈ {B},
      have h : ({A, B} : Set) = {A}, rw mem_singleton at h, apply ext, simp only [mem_insert, mem_singleton], finish,
      rw [h, card_singleton, ←card_nat one_nat, countable_card], exact nat_countable one_nat,
    rw [card_insert h, card_singleton, card_add_one_eq_succ (finite_cardinal_iff_nat.mpr one_nat)],
    change two.card_le (card ω), rw [←card_nat two_nat, countable_card], exact nat_countable two_nat,
  intros z hz, rw [mem_insert, mem_singleton] at hz, finish,
end

theorem singleton_countable {A : Set} : countable {A} :=
begin
  rw countable_iff, exact or.inl singleton_finite,
end

theorem succ_countable {A : Set} (Ac : A.countable) : A.succ.countable :=
by rw succ; exact union_countable singleton_countable Ac

theorem countable_of_succ {A : Set} (Ac : A.succ.countable) : A.countable :=
sub_countable self_sub_succ Ac

lemma repl_img_dom {A : Set} {f : Set → Set} : repl_img f A ≼ A :=
begin
  apply dominates_of_onto_fun, use pair_sep_eq A (repl_img f A) f,
  refine ⟨pair_sep_eq_is_fun, pair_sep_eq_dom_eq _, pair_sep_eq_ran_eq _⟩,
    intros x xA, rw mem_repl_img, finish,
  apply of_repl_img, finish,
end

lemma repl_img_card_le {A : Set} {f : Set → Set} : (repl_img f A).card.card_le A.card :=
card_le_iff_equin'.mpr repl_img_dom

lemma dom_trans {A B : Set} (AB : A ≼ B) {C : Set} (BC : B ≼ C) : A ≼ C :=
by rw ←card_le_iff_equin' at AB BC ⊢; exact card_le_trans ⟨_, rfl⟩ AB BC

lemma repl_img_countable {A : Set} (Ac : A.countable) {f : Set → Set} : (repl_img f A).countable :=
dom_trans repl_img_dom Ac

theorem countable_of_mem_countable_ord {α : Set} (αord : α.is_ordinal) (αc : α.countable)
  {β : Set} (βα : β ∈ α) : β.countable :=
sub_countable ((ord_le_iff_sub (ord_of_mem_ord αord βα) αord).mp (or.inl βα)) αc

theorem ord_add_countable {α : Set} (αord : α.is_ordinal) (αc : α.countable)
  {β : Set} (βord : β.is_ordinal) (βc : β.countable) : (α.ord_add β).countable :=
begin
  revert β, apply @trans_ind_schema (λ β, β.countable → (α.ord_add β).countable),
  intros β βord ind βc, dsimp at ind, rcases ord_cases βord with (βz|(⟨δ, βδ⟩|βord')),
  { subst βz, rw ord_add_zero αord, exact αc, },
  { subst βδ, have δord := ord_of_succ_ord βord, rw ord_add_succ αord δord,
    exact succ_countable (ind self_mem_succ (countable_of_succ βc)), },
  { rw ord_add_limit αord βord', exact Union_countable (repl_img_countable βc)
      (of_repl_img (λ δ δβ, ind δβ (countable_of_mem_countable_ord βord βc δβ))), },
end

theorem ord_mul_countable {α : Set} (αord : α.is_ordinal) (αc : α.countable)
  {β : Set} (βord : β.is_ordinal) (βc : β.countable) : (α.ord_mul β).countable :=
begin
  revert β, apply @trans_ind_schema (λ β, β.countable → (α.ord_mul β).countable),
  intros β βord ind βc, dsimp at ind, rcases ord_cases βord with (βz|(⟨δ, βδ⟩|βord')),
  { subst βz, rw ord_mul_zero αord, exact nat_countable zero_nat, },
  { subst βδ, have δord := ord_of_succ_ord βord, rw ord_mul_succ αord δord,
    exact ord_add_countable (ord_mul_ord αord δord) (ind self_mem_succ (countable_of_succ βc)) αord αc, },
  { rw ord_mul_limit αord βord', exact Union_countable (repl_img_countable βc)
      (of_repl_img (λ δ δβ, ind δβ (countable_of_mem_countable_ord βord βc δβ))), },
end

theorem ord_exp_countable {α : Set} (αord : α.is_ordinal) (αc : α.countable)
  {β : Set} (βord : β.is_ordinal) (βc : β.countable) : (α.ord_exp β).countable :=
begin
  revert β, apply @trans_ind_schema (λ β, β.countable → (α.ord_exp β).countable),
  intros β βord ind βc, dsimp at ind, rcases ord_cases βord with (βz|(⟨δ, βδ⟩|βord')),
  { subst βz, rw ord_exp_zero, exact nat_countable one_nat, },
  { subst βδ, have δord := ord_of_succ_ord βord, rw ord_exp_succ δord,
    exact ord_mul_countable (ord_exp_ord αord δord) (ind self_mem_succ (countable_of_succ βc)) αord αc, },
  { by_cases αz : α = ∅,
      subst αz, rw ord_exp_base_zero βord'.ne, exact nat_countable zero_nat,
    rw ord_exp_limit αz βord', exact Union_countable (repl_img_countable βc)
      (of_repl_img (λ δ δβ, ind δβ (countable_of_mem_countable_ord βord βc δβ))), },
end

end Set