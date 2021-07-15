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
      refine ⟨ℵ₀, ⟨⟨_, rfl⟩, aleph_null_infinite_cardinal⟩, _⟩,
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
theorem Aleph_lt_of_mem {α β : Set} (βord : β.is_ordinal) (αβ : α ∈ β) : α.Aleph.card_lt β.Aleph :=
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

lemma Aleph_zero_eq : Aleph ∅ = ℵ₀ :=
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
    then ℵ₀
  else if ex₁ : ∃ α : Set, α.is_ordinal ∧ f.dom = α.succ
    then card_exp two (f.fun_value (classical.some ex₁))
  else if ex₂ : ∃ γ : Set, γ.limit_ord ∧ f.dom = γ
    then f.ran.Union
  else ∅)
lemma beth_fun_empty {f : Set} (fdom : f.dom = ∅) : beth_fun f = ℵ₀ :=
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
lemma beth_zero : beth ∅ = ℵ₀ :=
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

def continuum_hypothesis : Prop := one.Aleph = one.beth
def generalized_continuum_hypothesis : Prop := ∀ α : Set, α.is_ordinal → α.Aleph = α.beth

end Set