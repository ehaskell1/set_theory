import ch6_cont
universe u
namespace Set

local attribute [irreducible] mem
local attribute [instance] classical.prop_decidable

lemma finite_lin_order_is_well_order {A R : Set.{u}} (Afin : A.is_finite) (lin : A.lin_order R) : A.well_order R :=
begin
  rw well_order_iff_not_exists_desc_chain lin, rintro ⟨f, finto, hd⟩,
  refine nat_infinite (finite_of_dominated_by_finite Afin ⟨_, finto, _⟩),
  have h : ∀ {n : Set.{u}}, n ∈ nat.{u} → ∀ {m : Set}, m ∈ nat.{u} → n ∈ m → (f.fun_value m).pair (f.fun_value n) ∈ R,
    intros n nω m mω nm, rw lt_iff nω mω at nm, rcases nm with ⟨k, kω, nkm⟩, subst nkm, clear mω, revert k,
    refine @induction _ _ _,
      rw [add_ind nω zero_nat, add_base nω], exact hd nω,
    intros k kω ind,
    have kω' := nat_induct.succ_closed kω,
    rw add_ind nω kω', exact lin.trans (hd (add_into_nat nω kω')) ind,
  apply one_to_one_of finto.left, rw finto.right.left,
  intros m mω n nω mn fmn,
  obtain (mln|nlm) := nat_order_conn mω nω mn,
    specialize h mω nω mln, rw fmn at h, exact lin.irrefl h,
  specialize h nω mω nlm, rw fmn at h, exact lin.irrefl h,
end

lemma exists_smallest {A R : Set} (Ane : A ≠ ∅) (Afin : A.is_finite) (lin : A.lin_order R) :
  ∃ x : Set, x ∈ A ∧ ∀ {y : Set}, y ∈ A → y ≠ x → x.pair y ∈ R :=
begin
  obtain ⟨x, xA, xle⟩ := (finite_lin_order_is_well_order Afin lin).well Ane subset_self,
  refine ⟨x, xA, λ y yA yx, _⟩, apply classical.by_contradiction, intro xy, apply xle,
  cases lin.conn yA xA yx with yx xy',
    exact ⟨_, yA, yx⟩,
  exfalso, exact xy xy',
end

noncomputable def smallest (A R : Set) : Set :=
if Ane : A ≠ ∅ then
if fin : A.is_finite then
if lin : A.lin_order R then
classical.some (exists_smallest Ane fin lin)
else ∅ else ∅ else ∅
lemma smallest_mem {A R : Set} (Ane : A ≠ ∅) (Afin : A.is_finite) (lin : A.lin_order R) :
  A.smallest R ∈ A :=
begin
  rw [smallest, dif_pos Ane, dif_pos Afin, dif_pos lin],
  obtain ⟨xA, h⟩ := classical.some_spec (exists_smallest Ane Afin lin), exact xA,
end
lemma smallest_smallest {A R : Set} (Ane : A ≠ ∅) (Afin : A.is_finite) (lin : A.lin_order R)
  {y : Set} (yA : y ∈ A) (yx : y ≠ A.smallest R) : (A.smallest R).pair y ∈ R :=
begin
  rw [smallest, dif_pos Ane, dif_pos Afin, dif_pos lin] at yx ⊢,
  obtain ⟨xA, h⟩ := classical.some_spec (exists_smallest Ane Afin lin), exact h yA yx,
end

lemma finite_lin_order_iso_nat {A : Set} (fin : A.is_finite)
  {R : Set} (Rlin : A.lin_order R) : isomorphic A.card.eps_order_struct ⟨A, R, Rlin.rel⟩ :=
begin
  revert A,
  have h : ∀ {n : Set}, n ∈ ω → ∀ {A : Set}, A.card = n →
    ∀ {R : Set}, ∀ (Rlin : A.lin_order R), isomorphic n.eps_order_struct ⟨A, R, Rlin.rel⟩,
    refine @induction _ _ _,
      intros A Acard R Rlin,
      have Ae := eq_empty_of_card_empty Acard, subst Ae,
      refine ⟨_, empty_corr_empty, _⟩, dsimp, intros x y xe,
      exfalso, exact mem_empty _ xe,
    intros n nω ind A Acard R Rlin,
    have Ane : A ≠ ∅, apply ne_empty_of_zero_mem_card, rw Acard, exact zero_mem_succ nω,
    have Afin : A.is_finite, rw finite_iff, exact ⟨_, nat_induct.succ_closed nω, Acard⟩,
    let x := A.smallest R,
    let B := A \ {x},
    have ABx : A = B ∪ {x} := (diff_singleton_union_eq (smallest_mem Ane Afin Rlin)).symm,
    have Bcard : B.card = n,
      have Bfin : B.is_finite := subset_finite_of_finite Afin subset_diff,
      rw finite_iff at Bfin, rcases Bfin with ⟨m, mω, Bm⟩, rw Bm,
      apply cancel_add_right mω nω one_nat,
      rw [←succ_eq_add_one nω, ←Acard, ABx,
        ←card_add_eq_ord_add ⟨_, nat_finite mω, card_nat mω⟩ ⟨_, nat_finite one_nat, card_nat one_nat⟩,
        ←Bm, ←@card_singleton x, ←card_add_spec rfl rfl],
      rw [←@self_inter_diff_empty {x} A, inter_comm],
    let S := R \ (prod {x} A),
    have Slin : B.lin_order S, split,
      { simp only [subset_def, mem_diff, mem_prod, exists_prop, mem_singleton, mem_diff],
        rintros z ⟨zR, h⟩, have zA : z ∈ A.prod A := Rlin.rel zR,
        rw mem_prod at zA, rcases zA with ⟨a, aA, b, bA, zab⟩, subst zab,
        refine ⟨_, ⟨aA, λ ax, h ⟨_, ax, _, bA, rfl⟩⟩, _, ⟨bA, λ bx, _⟩, rfl⟩,
        refine not_lt_and_gt_part (part_order_of_lin_order Rlin) ⟨zR, _⟩,
        rw bx, apply smallest_smallest Ane Afin Rlin aA, intro ax, rw [bx, ax] at zR,
        exact Rlin.irrefl zR, },
      { intros a b c ab bc, rw [mem_diff, pair_mem_prod, mem_singleton] at ab bc ⊢,
        refine ⟨Rlin.trans ab.left bc.left, _⟩, rintro ⟨ax, cA⟩, apply ab.right,
        have abA : a.pair b ∈ A.prod A := Rlin.rel ab.left,
        rw pair_mem_prod at abA, exact ⟨ax, abA.right⟩, },
      { intros x xx, rw mem_diff at xx, exact Rlin.irrefl xx.left, },
      { intros a b aB bB ab, simp only [mem_diff, pair_mem_prod, mem_singleton] at aB bB ⊢,
        cases Rlin.conn aB.left bB.left ab,
          exact or.inl ⟨h, λ h, aB.right h.left⟩,
        exact or.inr ⟨h, λ h, bB.right h.left⟩, },
    specialize ind Bcard Slin, rcases ind with ⟨f, ⟨fonto, foto⟩, fiso⟩, dsimp at fiso fonto,
    have de : (pair_sep_eq n.succ A (λ k, if k = ∅ then x else f.fun_value (pred.fun_value k))).dom = n.succ,
      apply pair_sep_eq_dom_eq, intros k kn, dsimp,
      have kω : k ∈ ω := mem_nat_of_mem_nat_of_mem (nat_induct.succ_closed nω) kn,
      by_cases kz : k = ∅,
        subst kz, rw if_pos rfl, exact smallest_mem Ane Afin Rlin,
      rw if_neg kz, obtain ⟨k', kω', kk'⟩ := or.resolve_left (exists_pred kω) kz, subst kk',
      rw pred_succ_eq_self kω',
      have fkB : f.fun_value k' ∈ B, rw ←fonto.right.right, apply fun_value_def'' fonto.left,
        rw [fonto.right.left, mem_iff_succ_mem_succ kω' nω], exact kn,
      rw mem_diff at fkB, exact fkB.left,
    refine ⟨pair_sep_eq n.succ A (λ k, if k = ∅ then x else f.fun_value (pred.fun_value k)),
      ⟨⟨pair_sep_eq_is_fun, de, pair_sep_eq_ran_eq _⟩, pair_sep_eq_oto _⟩, _⟩,
    { intros y yA, by_cases yx : y = x,
        refine ⟨_, zero_mem_succ nω, _⟩, dsimp, rw if_pos rfl, exact yx,
      have yB : y ∈ B, rw [mem_diff, mem_singleton], exact ⟨yA, yx⟩,
      rw [←fonto.right.right, mem_ran_iff fonto.left, fonto.right.left] at yB,
      rcases yB with ⟨k, kn, yk⟩,
      have kω := mem_nat_of_mem_nat_of_mem nω kn, subst yk, refine ⟨_, (mem_iff_succ_mem_succ kω nω).mp kn, _⟩,
      dsimp, rw [if_neg succ_neq_empty, pred_succ_eq_self kω], },
    { intros m mn k kn fmk,
      have kω := mem_nat_of_mem_nat_of_mem (nat_induct.succ_closed nω) kn,
      have mω := mem_nat_of_mem_nat_of_mem (nat_induct.succ_closed nω) mn,
      dsimp at fmk,
      by_cases mz : m = ∅, subst mz, rw if_pos rfl at fmk,
        by_cases kz : k = ∅, subst kz,
        rw if_neg kz at fmk, obtain ⟨k', kω', kk'⟩ := or.resolve_left (exists_pred kω) kz, subst kk',
        rw pred_succ_eq_self kω' at fmk,
        have xB : x ∈ B, rw [←fonto.right.right, mem_ran_iff fonto.left, fonto.right.left],
          use k', rw mem_iff_succ_mem_succ kω' nω, exact ⟨kn, fmk⟩,
        rw [mem_diff, mem_singleton] at xB, exfalso, exact xB.right rfl,
      rw if_neg mz at fmk, obtain ⟨m', mω', mm'⟩ := or.resolve_left (exists_pred mω) mz, subst mm',
      rw pred_succ_eq_self mω' at fmk,
      by_cases kz : k = ∅,
        subst kz, rw if_pos rfl at fmk,
        have xB : x ∈ B, rw [←fonto.right.right, mem_ran_iff fonto.left, fonto.right.left],
          use m', rw mem_iff_succ_mem_succ mω' nω, exact ⟨mn, fmk.symm⟩,
        rw [mem_diff, mem_singleton] at xB, exfalso, exact xB.right rfl,
      rw if_neg kz at fmk, obtain ⟨k', kω', kk'⟩ := or.resolve_left (exists_pred kω) kz, subst kk',
      rw pred_succ_eq_self kω' at fmk, congr,
      rw ←mem_iff_succ_mem_succ mω' nω at mn, rw ←mem_iff_succ_mem_succ kω' nω at kn,
      rw ←fonto.right.left at mn kn, exact from_one_to_one fonto.left foto mn kn fmk, },
    { rw [eps_order_struct_fld, eps_order_struct_rel], dsimp, intros m k mn kn,
      have kω := mem_nat_of_mem_nat_of_mem (nat_induct.succ_closed nω) kn,
      have mω := mem_nat_of_mem_nat_of_mem (nat_induct.succ_closed nω) mn,
      rw [pair_mem_eps_order' mn kn], rw ←de at mn kn,
      rw [pair_sep_eq_fun_value mn, pair_sep_eq_fun_value kn], dsimp, rw de at mn kn,
      by_cases kz : k = ∅,
        subst kz, rw if_pos rfl,
        by_cases mz : m = ∅,
          subst mz, rw if_pos rfl, split,
            intro ee, exfalso, exact mem_empty _ ee,
          intro xx, exfalso, exact Rlin.irrefl xx,
        rw if_neg mz, obtain ⟨m', mω', mm'⟩ := or.resolve_left (exists_pred mω) mz, subst mm',
        rw pred_succ_eq_self mω', split,
          intro mz', exfalso, exact mem_empty _ mz',
        intro fmx,
        have fmA : f.fun_value m' ∈ B, rw ←fonto.right.right,
          apply fun_value_def'' fonto.left, rw [fonto.right.left, mem_iff_succ_mem_succ mω' nω],
          exact mn,
        rw [mem_diff, mem_singleton] at fmA, exfalso,
        exact not_lt_and_gt_part (part_order_of_lin_order Rlin) ⟨fmx, smallest_smallest Ane Afin Rlin fmA.left fmA.right⟩,
      rw if_neg kz, obtain ⟨k', kω', kk'⟩ := or.resolve_left (exists_pred kω) kz, subst kk',
      rw pred_succ_eq_self kω',
      by_cases mz : m = ∅,
        subst mz, rw if_pos rfl,
        have fkB : f.fun_value k' ∈ B, rw ←fonto.right.right, apply fun_value_def'' fonto.left,
          rw [fonto.right.left, mem_iff_succ_mem_succ kω' nω], exact kn,
        rw [mem_diff, mem_singleton] at fkB, split,
          intro zk, exact smallest_smallest Ane Afin Rlin fkB.left fkB.right,
        intro xfk, exact zero_mem_succ kω',
      rw if_neg mz, obtain ⟨m', mω', mm'⟩ := or.resolve_left (exists_pred mω) mz, subst mm',
      rw [pred_succ_eq_self mω', ←mem_iff_succ_mem_succ mω' kω'],
      rw ←mem_iff_succ_mem_succ mω' nω at mn, rw ←mem_iff_succ_mem_succ kω' nω at kn,
      specialize fiso mn kn, rw [pair_mem_eps_order' mn kn, mem_diff] at fiso, rw fiso,
      simp only [pair_mem_prod, not_and, and_iff_left_iff_imp, mem_singleton],
      intros fmk fmx fkA,
      have fmB : f.fun_value m' ∈ B, rw ←fonto.right.right, apply fun_value_def'' fonto.left,
        rw fonto.right.left, exact mn,
      rw [mem_diff, mem_singleton] at fmB, exact fmB.right fmx, },
  intros A Afin Rlin,
  rw finite_iff at Afin, rcases Afin with ⟨n, nω, Acard⟩,
  rw Acard, exact h nω Acard Rlin,
end

-- problem 19 chapter 7
lemma finite_lin_order_iso {A : Set} (fin : A.is_finite)
  {R : Set} (Rlin : A.lin_order R) {S : Set} (Slin : A.lin_order S) :
  isomorphic ⟨A, R, Rlin.rel⟩ ⟨A, S, Slin.rel⟩ :=
iso_trans (iso_symm (finite_lin_order_iso_nat fin Rlin)) (finite_lin_order_iso_nat fin Slin)

-- chapter 7 exercise 20
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

-- end of chapter 7 starting from page 199

lemma card_is_ord {κ : Set} (κcard : κ.is_cardinal) : κ.is_ordinal :=
begin
  rcases κcard with ⟨K, Kcard⟩, rw ←Kcard, exact card_is_ordinal,
end

lemma card_is_ord' {A : Set} : A.card.is_ordinal :=
card_is_ord ⟨_, rfl⟩

lemma card_lt_of_mem {κ : Set} (κcard : κ.is_cardinal) {μ : Set} (μcard : μ.is_cardinal) (κμ : κ ∈ μ) : κ.card_lt μ :=
begin
  have κord := card_is_ord κcard,
  have μord := card_is_ord μcard,
  rw ord_mem_iff_ssub κord μord at κμ,
  rw card_lt, refine ⟨_, κμ.right⟩,
  rw [←card_of_cardinal_eq_self κcard, ←card_of_cardinal_eq_self μcard],
  exact card_le_of_subset κμ.left,
end

lemma not_card_lt_of_not_mem {κ : Set} (κcard : κ.is_cardinal) {μ : Set} (μcard : μ.is_cardinal) (κμ : κ ∉ μ) : ¬ κ.card_lt μ :=
begin
  have κord := card_is_ord κcard,
  have μord := card_is_ord μcard,
  rw ←ord_not_le_iff_lt μord κord at κμ, push_neg at κμ,
  have μκ : μ.card_le κ, cases κμ,
      exact (card_lt_of_mem μcard κcard κμ).left,
    subst κμ, exact card_le_refl,
  intro lt,
  exact lt.right (card_eq_of_le_of_le κcard μcard lt.left μκ),
end

lemma card_lt_iff_mem {κ : Set} (κcard : κ.is_cardinal) {μ : Set} (μcard : μ.is_cardinal) : κ.card_lt μ ↔ κ ∈ μ :=
⟨λ κμ, classical.by_contradiction (λ nκμ, (not_card_lt_of_not_mem κcard μcard nκμ) κμ), card_lt_of_mem κcard μcard⟩

lemma card_le_iff_le {κ : Set} (κcard : κ.is_cardinal) {μ : Set} (μcard : μ.is_cardinal) : κ.card_le μ ↔ κ ≤ μ :=
by rw [card_le_iff, le_iff, card_lt_iff_mem κcard μcard]

lemma ord_dom_of_le {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal)
  (αβ : α ≤ β) : α ≼ β :=
begin
  rw ord_le_iff_sub αord βord at αβ, rw dominated_iff,
  exact ⟨_, αβ, equin_refl⟩,
end

lemma ord_lt_of_card_lt {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal)
  (lt : α.card.card_lt β.card) : α ∈ β :=
begin
  rw card_lt_iff at lt, rw ←ord_not_le_iff_lt βord αord, intro le, apply lt.right,
  exact equin_of_dom_of_dom lt.left (ord_dom_of_le βord αord le),
end

-- problem 24 lemma
lemma ord_mem_card_powerset {α : Set} (αord : α.is_ordinal) : α ∈ α.powerset.card :=
begin
  apply ord_lt_of_card_lt αord card_is_ord', rw [card_of_cardinal_eq_self ⟨_, rfl⟩, card_power],
  exact card_lt_exp ⟨_, rfl⟩,
end

-- problem 24
lemma exists_larger_card {α : Set} (αord : α.is_ordinal) : ∃ κ : Set, κ.is_cardinal ∧ α ∈ κ :=
⟨_, ⟨_, rfl⟩, ord_mem_card_powerset αord⟩

-- problem 25
lemma trans_ind_schema {φ : Set → Prop} (ind : ∀ {α : Set}, α.is_ordinal → (∀ {x : Set}, x ∈ α → φ x) → φ α)
  (α : Set) (αord : α.is_ordinal) : φ α :=
begin
  let X := {x ∈ α.succ | φ x},
  have Xα : X = α.succ,
    apply transfinite_ind (ordinal_well_ordered (succ_ord_of_ord αord)) sep_subset,
    intros t tα hi, rw mem_sep, refine ⟨tα, ind (ord_of_mem_ord (succ_ord_of_ord αord) tα) _⟩,
    intros x xt,
    suffices xX : x ∈ X, rw mem_sep at xX, exact xX.right,
    apply hi, rw [mem_seg, eps_order, pair_mem_pair_sep' (ord_mem_trans (succ_ord_of_ord αord) xt tα) tα],
    exact xt,
  suffices h : α ∈ X, rw mem_sep at h, exact h.right,
  rw Xα, exact self_mem_succ,
end

def init_ord (α : Set) : Prop := α.is_ordinal ∧ ¬ ∃ β : Set, β ∈ α ∧ α ≈ β

theorem init_iff_card {α : Set} : α.init_ord ↔ α.is_cardinal :=
begin
  split,
    intro init, use α, symmetry, apply eq_card init.left equin_refl,
    intros β βord αβ, apply classical.by_contradiction, intro le,
    rw ord_not_le_iff_lt init.left βord at le, exact init.right ⟨_, le, αβ⟩,
  intro αcard,
  have eq := card_of_cardinal_eq_self αcard, rw ←eq, refine ⟨card_is_ordinal, _⟩,
  rintro ⟨β, βA, Aβ⟩,
  have βord := ord_of_mem_ord card_is_ordinal βA,
  rw ←ord_not_le_iff_lt card_is_ordinal βord at βA,
  rw eq at Aβ, apply βA, exact card_least βord Aβ,

end

lemma omega_is_card : is_cardinal ω :=
begin
  rw ←init_iff_card, split,
    exact omega_is_ord,
  rintro ⟨n, nω, ωn⟩, exact nat_infinite ⟨_, nω, ωn⟩,
end

lemma exists_powersets (X : Set) : ∃ B : Set, ∀ (y : Set), y ∈ B ↔ ∃ x : Set, x ∈ X ∧ y = x.powerset :=
replacement'' powerset
noncomputable def powersets (X : Set.{u}) : Set.{u} := classical.some X.exists_powersets
lemma mem_powersets {X y : Set} : y ∈ X.powersets ↔ ∃ x : Set, x ∈ X ∧ y = x.powerset :=
classical.some_spec X.exists_powersets y

lemma L7Q {δ : Set} (δord : δ.is_ordinal) :
  ∃ F : Set, F.is_function ∧ F.dom = δ ∧ ∀ ⦃α : Set⦄, α ∈ δ → F.fun_value α = ((F.img α).powersets).Union :=
begin
  obtain ⟨F, Ffun, Fdom, Fspec⟩ := exists_of_exists_unique (@transfinite_rec' δ δ.eps_order (ordinal_well_ordered δord) (fun x, x.ran.powersets.Union)),
  refine ⟨_, Ffun, Fdom, λ α αδ, _⟩, specialize Fspec αδ, rw Fspec,
  dsimp, rw [restrict_ran, seg_eq_of_trans (ordinal_trans δord) αδ],
end

noncomputable def L7Q_fun (δ : Set) : Set := if δord : δ.is_ordinal then classical.some (L7Q δord) else ∅
lemma L7Q_fun_spec {δ : Set} (δord : δ.is_ordinal) :
  δ.L7Q_fun.is_function ∧ δ.L7Q_fun.dom = δ ∧ ∀ ⦃α : Set⦄, α ∈ δ → δ.L7Q_fun.fun_value α = ((δ.L7Q_fun.img α).powersets).Union :=
begin
  simp [L7Q_fun, dif_pos δord], exact classical.some_spec (L7Q δord),
end

lemma L7R : ∀ {δ : Set}, δ.is_ordinal → ∀ {ε : Set}, ε.is_ordinal →
  ∀ {α : Set}, α ∈ δ ∩ ε → δ.L7Q_fun.fun_value α = ε.L7Q_fun.fun_value α :=
begin
  have h₁ : ∀ {δ : Set}, δ.is_ordinal → ∀ {α : Set}, α ∈ δ → ∀ {z : Set}, z ∈ (δ.L7Q_fun.img α).powersets ↔ ∃ β : Set, β ∈ α ∧ z = (δ.L7Q_fun.fun_value β).powerset,
    intros δ δord α αδ z, rw mem_powersets,
    have αord : α.is_ordinal := ord_of_mem_ord δord αδ,
    rw ord_mem_iff_ssub αord δord at αδ,
    obtain ⟨δfun, δdom, -⟩ := L7Q_fun_spec δord, rw ←δdom at αδ, simp only [mem_img' δfun αδ.left], split,
      rintro ⟨y, ⟨β, βα, yfβ⟩, zy⟩, subst yfβ, exact ⟨_, βα, zy⟩,
    rintro ⟨β, βα, zf⟩, exact ⟨_, ⟨_, βα, rfl⟩, zf⟩,
  have h₂ : ∀ {δ : Set}, δ.is_ordinal → ∀ {ε : Set}, ε.is_ordinal → δ ⊆ ε → {α ∈ δ | δ.L7Q_fun.fun_value α = ε.L7Q_fun.fun_value α} = δ,
    intros δ δord ε εord δε, apply transfinite_ind (ordinal_well_ordered δord) sep_subset,
    obtain ⟨-, -, δspec⟩ := L7Q_fun_spec δord, obtain ⟨-, -, εspec⟩ := L7Q_fun_spec εord,
    intros α αδ ind, rw [mem_sep, δspec αδ, εspec (δε αδ)], refine ⟨αδ, _⟩,
    congr' 1, apply ext, simp only [h₁ δord αδ, h₁ εord (δε αδ)], intro z, apply exists_congr,
    intro β, rw and.congr_right_iff, intro βα,
    suffices hβ : β ∈ δ.eps_order.seg α, specialize ind hβ, rw mem_sep at ind, rw ind.right,
    rw [mem_seg, eps_order, pair_mem_pair_sep' (ord_mem_trans δord βα αδ) αδ], exact βα,
  intros δ δord ε εord α hα, cases ord_conn' δord εord,
    rw ord_le_iff_sub δord εord at h, rw inter_eq_of_sub h at hα,
    specialize h₂ δord εord h, rw [←h₂, mem_sep] at hα, exact hα.right,
  rw ord_le_iff_sub εord δord at h, rw [inter_comm, inter_eq_of_sub h] at hα,
  specialize h₂ εord δord h, rw [←h₂, mem_sep] at hα, exact hα.right.symm,
end

noncomputable def Veb (α : Set) : Set := α.succ.L7Q_fun.fun_value α
noncomputable def Veb_img (α : Set) : Set :=
classical.some (@replacement'' Veb α)
lemma mem_Veb_img {α V : Set} : V ∈ α.Veb_img ↔ ∃ β : Set, β ∈ α ∧ V = β.Veb :=
classical.some_spec (@replacement'' Veb α)

-- Theorem 7S
theorem Veb_eq {α : Set} (αord : α.is_ordinal) : α.Veb = α.Veb_img.powersets.Union :=
begin
  obtain ⟨f, dom, spec⟩ := L7Q_fun_spec (succ_ord_of_ord αord),
  rw [Veb, spec self_mem_succ], congr, apply ext, intro V,
  have subdom : α ⊆ α.succ.L7Q_fun.dom, rw dom, exact self_sub_succ,
  simp only [mem_img' f subdom, mem_Veb_img, Veb], apply exists_congr,
  intro β, rw and.congr_right_iff, intro βα, apply eq.congr_right,
  apply L7R (succ_ord_of_ord αord) (succ_ord_of_ord (ord_of_mem_ord αord βα)),
  rw mem_inter, refine ⟨_, self_mem_succ⟩, rw [succ, mem_union], right, exact βα,
end

lemma mem_Veb {α : Set} (αord : α.is_ordinal) {X : Set} : X ∈ α.Veb ↔ ∃ β : Set, β ∈ α ∧ X ⊆ β.Veb :=
begin
  simp only [Veb_eq αord, mem_Union, exists_prop, mem_powersets, mem_Veb_img], split,
    rintro ⟨Y, ⟨V, ⟨β, βα, Vβ⟩, YV⟩, XY⟩, subst Vβ, subst YV, rw mem_powerset at XY, exact ⟨_, βα, XY⟩,
  rintro ⟨β, βα, Xβ⟩, refine ⟨_, ⟨_, ⟨_, βα, rfl⟩, rfl⟩, _⟩, rw mem_powerset, exact Xβ,
end

-- Theorem 7T
theorem Veb_transitive : ∀ {α : Set}, α.is_ordinal → α.Veb.transitive_set :=
begin
  refine trans_ind_schema _, intros α αord hi, rw transitive_set_iff', intros X XV,
  simp only [Veb_eq αord, mem_Union, exists_prop, mem_powersets, mem_Veb_img] at XV,
  rcases XV with ⟨S, ⟨V, ⟨β, βα, Vβ⟩, SV⟩, XS⟩, subst SV, subst Vβ,
  have h := powerset_transitive (hi βα), rw transitive_set_iff' at h,
  specialize h XS, apply subset_trans h, intros Z Zβ,
  simp only [Veb_eq αord, mem_Union, exists_prop, mem_powersets, mem_Veb_img],
  exact ⟨_, ⟨_, ⟨_, βα, rfl⟩, rfl⟩, Zβ⟩,
end

structure limit_ord (α : Set) : Prop :=
(ord : α.is_ordinal)
(ne : α ≠ ∅)
(ns : ¬ ∃ β : Set, α = β.succ)

lemma succ_mem_limit {γ : Set} (γord : γ.limit_ord) {β : Set} (βγ : β ∈ γ) : β.succ ∈ γ :=
begin
  cases succ_least_upper_bound γord.ord βγ,
    exact h,
  exfalso, exact γord.ns ⟨_, h.symm⟩,
end

lemma limit_ord_of_not_bound {γ : Set} (γord : γ.is_ordinal) (γne : γ ≠ ∅)
  (h : ¬ ∃ β : Set, β ∈ γ ∧ ∀ {α : Set}, α ∈ γ → α ≤ β) : γ.limit_ord :=
begin
  refine ⟨γord, γne, _⟩, rintro ⟨β, βγ⟩, apply h, subst βγ, refine ⟨_, self_mem_succ, λ α αβ, _⟩,
  rw ←mem_succ_iff_le, exact αβ,
end

lemma limit_ord_not_bounded {γ : Set} (γord : γ.limit_ord) :
  ¬ ∃ β : Set, β ∈ γ ∧ ∀ {α : Set}, α ∈ γ → α ≤ β :=
begin
  rintro ⟨β, βγ, h⟩,
  specialize h (succ_mem_limit γord βγ),
  have βord := ord_of_mem_ord γord.ord βγ,
  rw ←ord_not_lt_iff_le βord (succ_ord_of_ord βord) at h,
  exact h self_mem_succ,
end

lemma limit_ord_inf {γ : Set} (γord : γ.limit_ord) : ¬ γ.is_finite :=
begin
  apply inf_of_sup_inf nat_infinite, rw subset_def,
  apply induction,
    rw ←ord_not_le_iff_lt γord.ord (nat_is_ord zero_nat), rintro (h|h),
      exact mem_empty _ h,
    exact γord.ne h,
  intros n nω nγ, exact succ_mem_limit γord nγ,
end

-- Theorem 7U part a
theorem Veb_sub_of_mem {β α : Set} (αord : α.is_ordinal) (βα : β ∈ α) : β.Veb ⊆ α.Veb :=
begin
  intros X Xβ, rw mem_Veb αord,
  have βord := ord_of_mem_ord αord βα,
  have trans := Veb_transitive βord, rw transitive_set_iff' at trans,
  exact ⟨_, βα, trans Xβ⟩,
end

-- Theorem 7U part b
theorem Veb_null_eq_null : Veb ∅ = ∅ :=
begin
  rw eq_empty, intros z zV, rw mem_Veb zero_is_ord at zV,
  rcases zV with ⟨β, βn, -⟩, exact mem_empty _ βn,
end

-- Theorem 7U part c
theorem Veb_succ_eq_powerset {α : Set} (αord : α.is_ordinal) : α.succ.Veb = α.Veb.powerset :=
begin
  apply ext, simp only [mem_Veb (succ_ord_of_ord αord), mem_powerset], intro X, split,
    rintro ⟨β, βα, Xβ⟩, rw [succ, mem_union, mem_singleton] at βα, cases βα,
      subst βα, exact Xβ,
    exact subset_trans Xβ (Veb_sub_of_mem αord βα),
  intro Xα, exact ⟨_, self_mem_succ, Xα⟩,
end

lemma mem_Union_Veb_img {α X : Set} : X ∈ α.Veb_img.Union ↔ ∃ β : Set, β ∈ α ∧ X ∈ β.Veb :=
begin
  simp only [mem_Union, exists_prop, mem_Veb_img], split,
    rintro ⟨V, ⟨β, βα, Vβ⟩, XV⟩, subst Vβ, exact ⟨_, βα, XV⟩,
  rintro ⟨β, βα, Xβ⟩, exact ⟨_, ⟨_, βα, rfl⟩, Xβ⟩,
end

-- Theorem 7U part d
theorem Veb_limit_ord_eq {γ : Set} (γord : γ.limit_ord) : γ.Veb = γ.Veb_img.Union :=
begin
  apply ext, simp only [mem_Veb γord.ord, mem_Union_Veb_img], intro X, split,
    rintro ⟨β, βγ, Xβ⟩, refine ⟨_, succ_mem_limit γord βγ, _⟩,
    rw [Veb_succ_eq_powerset (ord_of_mem_ord γord.ord βγ), mem_powerset], exact Xβ,
  rintro ⟨β, βγ, Xβ⟩,
  have trans := Veb_transitive (ord_of_mem_ord γord.ord βγ),
  rw transitive_set_iff' at trans, exact ⟨_, βγ, trans Xβ⟩,
end

lemma exists_least_ord_of_exists {p : Set → Prop} (h : ∃ α : Set, α.is_ordinal ∧ p α) :
  ∃ α : Set, α.is_ordinal ∧ p α ∧ ∀ {β : Set}, β.is_ordinal → p β → α ≤ β :=
begin
  rcases h with ⟨α, αord, pα⟩,
  have αord' := succ_ord_of_ord αord,
  let X := {β ∈ α.succ | p β},
  have XE : X ≠ ∅, apply ne_empty_of_inhabited, use α, rw mem_sep, exact ⟨self_mem_succ, pα⟩,
  obtain ⟨γ, γX, h⟩ := (ordinal_well_ordered αord').well XE sep_subset,
  rw mem_sep at γX, refine ⟨_, ord_of_mem_ord αord' γX.left, γX.right, λ β, assume βord pβ, _⟩,
  apply classical.by_contradiction, intro γβ, apply h, use β,
  rw ord_not_le_iff_lt (ord_of_mem_ord αord' γX.left) βord at γβ,
  have βα := ord_mem_trans αord' γβ γX.left,
  rw [mem_sep, eps_order, pair_mem_pair_sep' βα γX.left],
  exact ⟨⟨βα, pβ⟩, γβ⟩,
end

def grounded (A : Set) : Prop := ∃ α : Set, α.is_ordinal ∧ A ⊆ α.Veb

noncomputable def rank (A : Set) : Set := if h : A.grounded then classical.some (exists_least_ord_of_exists h) else ∅
lemma rank_ord_of_grounded {A : Set} (Agr : A.grounded) : A.rank.is_ordinal :=
begin
  simp only [rank, dif_pos Agr],
  obtain ⟨h, -, -⟩ := classical.some_spec (exists_least_ord_of_exists Agr),
  exact h,
end
lemma rank_sub_of_grounded {A : Set} (Agr : A.grounded) : A ⊆ A.rank.Veb :=
begin
  simp only [rank, dif_pos Agr],
  obtain ⟨-, h, -⟩ := classical.some_spec (exists_least_ord_of_exists Agr),
  exact h,
end
lemma rank_least_of_grounded {A : Set} (Agr : A.grounded) : ∀ {β : Set}, β.is_ordinal → A ⊆ β.Veb → A.rank ≤ β :=
begin
  simp only [rank, dif_pos Agr],
  obtain ⟨-, -, h⟩ := classical.some_spec (exists_least_ord_of_exists Agr),
  exact @h,
end

lemma ord_not_sub_Veb {α : Set} (αord : α.is_ordinal) : ∀ {β : Set}, β ∈ α → ¬ (α ⊆ β.Veb) :=
begin
  revert α, refine trans_ind_schema _, intros α αord ind β βα αβ,
  suffices ββ : β ∉ β.Veb,
    exact ββ (αβ βα),
  rw mem_Veb (ord_of_mem_ord αord βα), rintro ⟨δ, δβ, βδ⟩,
  exact ind βα δβ βδ,
end

lemma ord_sub_Veb_self {α : Set} (αord : α.is_ordinal) : α ⊆ α.Veb :=
begin
  revert α, refine trans_ind_schema _, intros α αord ind β βα,
  specialize ind βα, rw mem_Veb αord, exact ⟨_, βα, ind⟩,
end

-- exercise 26
theorem ord_grounded {α : Set} (αord : α.is_ordinal) : α.grounded := ⟨_, αord, ord_sub_Veb_self αord⟩
theorem rank_ord_eq_self {α : Set} (αord : α.is_ordinal) : α.rank = α :=
begin
  have h := rank_least_of_grounded (ord_grounded αord) αord (ord_sub_Veb_self αord),
  cases h,
    exfalso, exact ord_not_sub_Veb αord h (rank_sub_of_grounded (ord_grounded αord)),
  exact h,
end

-- Theorem 7V part a part 1
theorem grounded_of_mem_grounded {A : Set} (Agr : A.grounded) {a : Set} (aA : a ∈ A) : a.grounded :=
begin
  obtain ⟨α, αord, Aα⟩ := Agr,
  have trans := Veb_transitive αord, rw transitive_set_iff' at trans,
  exact ⟨_, αord, trans (Aα aA)⟩,
end

-- Theorem 7V part a part 2
theorem rank_mem_of_mem_grounded {A : Set} (Agr : A.grounded) {a : Set} (aA : a ∈ A) : a.rank ∈ A.rank :=
begin
  have h : a ∈ A.rank.Veb := (rank_sub_of_grounded Agr) aA,
  have Aord : A.rank.is_ordinal := rank_ord_of_grounded Agr,
  rw mem_Veb Aord at h, rcases h with ⟨β, βA, aβ⟩,
  apply @ord_lt_of_le_of_lt _ β _ Aord,
    exact (rank_least_of_grounded (grounded_of_mem_grounded Agr aA) (ord_of_mem_ord Aord βA) aβ),
  exact βA,
end

lemma T7V_ord {A : Set} (hA : ∀ {a : Set}, a ∈ A → a.grounded) : (A.repl_img (succ ∘ rank)).Union.is_ordinal :=
begin
  apply Union_ords_is_ord, intros β βA,
  rw mem_repl_img at βA, rcases βA with ⟨a, aA, βa⟩, subst βa,
  apply succ_ord_of_ord (rank_ord_of_grounded (hA aA)),
end

lemma T7V_sub {A : Set} (hA : ∀ {a : Set}, a ∈ A → a.grounded) : A ⊆ (A.repl_img (succ ∘ rank)).Union.Veb :=
begin
  intros a aA,
  have aa : a ∈ a.rank.succ.Veb,
    rw [Veb_succ_eq_powerset (rank_ord_of_grounded (hA aA)), mem_powerset],
    exact rank_sub_of_grounded (hA aA),
  have aα : a.rank.succ ≤ (A.repl_img (succ ∘ rank)).Union,
    rw ord_le_iff_sub (succ_ord_of_ord (rank_ord_of_grounded (hA aA))) (T7V_ord @hA),
    apply subset_Union, rw mem_repl_img, exact ⟨_, aA, rfl⟩,
  cases aα,
    exact Veb_sub_of_mem (T7V_ord @hA) aα aa,
  rw ←aα, exact aa,
end

-- Theorem 7V part b part 1
theorem grounded_of_all_mem_grounded {A : Set} (hA : ∀ {a : Set}, a ∈ A → a.grounded) : A.grounded :=
⟨_, T7V_ord @hA, T7V_sub @hA⟩

-- Theorem 7V part b part 2
theorem rank_eq_of_all_mem_grounded {A : Set} (hA : ∀ {a : Set}, a ∈ A → a.grounded) : A.rank = (A.repl_img (succ ∘ rank)).Union :=
begin
  let α := (A.repl_img (succ ∘ rank)).Union,
  have Agr := grounded_of_all_mem_grounded @hA,
  rw ord_eq_iff_le_and_le (rank_ord_of_grounded Agr) (T7V_ord @hA), split,
    exact rank_least_of_grounded Agr (T7V_ord @hA) (T7V_sub @hA),
  have h₁ : ∀ {a : Set}, a ∈ A → a.rank.succ ≤ A.rank,
    intros a aA, exact succ_least_upper_bound (rank_ord_of_grounded Agr) (rank_mem_of_mem_grounded Agr aA),
  have h₂ : ∀ {β : Set}, β.is_ordinal →  (∀ {a : Set}, a ∈ A → a.rank.succ ≤ β) → α ≤ β,
    intros β βord hβ, rw ord_le_iff_sub (T7V_ord @hA) βord,
    intro δ, simp only [mem_Union, exists_prop, mem_repl_img],
    rintro ⟨Z, ⟨a, aA, Za⟩, δZ⟩, subst Za,
    specialize hβ aA, rw ord_le_iff_sub (succ_ord_of_ord (rank_ord_of_grounded (hA aA))) βord at hβ,
    exact hβ δZ,
  exact h₂ (rank_ord_of_grounded Agr) @h₁,
end

noncomputable def cl_fun (C : Set) : Set :=
trans_rec ω nat_order (λ f, C ∪ f.ran.Union.Union)
lemma cl_fun_fun {C : Set} : C.cl_fun.is_function := trans_rec_fun nat_well_order'
lemma cl_fun_dom {C : Set} : C.cl_fun.dom = ω := trans_rec_dom nat_well_order'

-- problem 7(b)
lemma cl_fun_lemma {C n : Set} (nω : n ∈ ω) {a : Set} (an : a ∈ C.cl_fun.fun_value n) : a ⊆ C.cl_fun.fun_value n.succ :=
begin
  have nω' := nat_induct.succ_closed nω,
  rw [cl_fun, trans_rec_spec nat_well_order' nω', nat_order_seg nω', restrict_ran],
  have h : n.succ ⊆ (trans_rec ω nat_order (λ f, C ∪ f.ran.Union.Union)).dom,
    rw trans_rec_dom nat_well_order', exact subset_nat_of_mem_nat nω',
  apply subset_union_of_subset_right, apply subset_Union,
  simp only [mem_Union, exists_prop, mem_img' (trans_rec_fun nat_well_order') h],
  rw cl_fun at an, exact ⟨_, ⟨_, self_mem_succ, rfl⟩, an⟩,
end

-- problem 7(c)
noncomputable def trans_cl (C : Set) : Set := C.cl_fun.ran.Union
lemma trans_cl_sub {C : Set} : C ⊆ C.trans_cl :=
begin
  apply subset_Union, simp only [cl_fun, mem_ran_iff (trans_rec_fun nat_well_order'), trans_rec_dom nat_well_order'], use ∅,
  simp only [trans_rec_spec nat_well_order' zero_nat, nat_order_seg zero_nat, restrict_empty, ran_empty_eq_empty, union_empty_eq_empty, union_empty],
  exact ⟨zero_nat, rfl⟩,
end
lemma trans_cl_trans {C : Set} : C.trans_cl.transitive_set :=
begin
  rw transitive_set_iff', intros a aC,
  simp only [trans_cl, mem_Union, exists_prop, mem_ran_iff cl_fun_fun, cl_fun_dom] at aC,
  rcases aC with ⟨y, ⟨n, nω, yn⟩, ay⟩, subst yn,
  replace ay := cl_fun_lemma nω ay,
  apply subset_trans ay, simp only [subset_def, trans_cl, mem_Union, exists_prop, mem_ran_iff cl_fun_fun, cl_fun_dom],
  intros y yn, exact ⟨_, ⟨_, nat_induct.succ_closed nω, rfl⟩, yn⟩,
end

def reg_axiom : Prop := ∀ {A : Set}, A ≠ ∅ → ∃ m : Set, m ∈ A ∧ m ∩ A = ∅

-- Theorem 7W
theorem all_grounded_equiv_reg : (∀ {A : Set.{u}}, A.grounded) ↔ reg_axiom.{u} :=
begin
  split,
    intros gr A Ane,
    let B := A.repl_img rank,
    have Bord : ∀ x : Set, x ∈ B → x.is_ordinal, simp only [mem_repl_img],
      rintros μ ⟨x, xA, μx⟩, subst μx, exact rank_ord_of_grounded gr,
    have Bne : B ≠ ∅, apply ne_empty_of_inhabited,
      replace Ane := inhabited_of_ne_empty Ane, rcases Ane with ⟨x, xA⟩,
      use x.rank, rw mem_repl_img, exact ⟨_, xA, rfl⟩,
    obtain ⟨μ, μB, le⟩ := exists_least_ord_of_nonempty Bord Bne,
    rw mem_repl_img at μB, rcases μB with ⟨m, mA, μm⟩, subst μm,
    refine ⟨_, mA, _⟩, rw eq_empty, intros x xmA, rw mem_inter at xmA,
    apply le, use x.rank, simp only [mem_repl_img, eps_order, pair_mem_pair_sep],
    exact ⟨⟨_, xmA.right, rfl⟩, ⟨_, xmA.right, rfl⟩, ⟨_, mA, rfl⟩, rank_mem_of_mem_grounded gr xmA.left⟩,
  intros reg, apply @classical.by_contradiction (∀ {A : Set}, A.grounded), intro h,
  push_neg at h, rcases h with ⟨c, cng⟩,
  let B := trans_cl {c},
  let A : Set := {x ∈ B | ¬ x.grounded},
  have Ane : A ≠ ∅, apply ne_empty_of_inhabited, use c, rw mem_sep, refine ⟨trans_cl_sub _, cng⟩,
    rw mem_singleton,
  obtain ⟨m, mA, miA⟩ := reg Ane,
  rw mem_sep at mA, apply mA.right, apply grounded_of_all_mem_grounded,
  intros x xm,
  have trans : B.transitive_set := trans_cl_trans, rw transitive_set_iff at trans,
  have xB : x ∈ B := trans mA.left xm,
  have xA : x ∉ A, intro xA, apply mem_empty x, rw [←miA, mem_inter], exact ⟨xm, xA⟩,
  rw mem_sep at xA, push_neg at xA, exact xA xB,
end

-- A proof of the regularity axiom
theorem regularity' : reg_axiom :=
begin
  intros A Ane,
  have h := regularity _ Ane,
  simp only [exists_prop] at h, simp only [inter_comm], exact h,
end

theorem all_grounded : ∀ {x : Set}, x.grounded :=
begin
  rw all_grounded_equiv_reg, exact @regularity',
end

-- Theorem 7X(a)
theorem not_mem_self {A : Set} : A ∉ A :=
begin
  intro AA,
  obtain ⟨m, mA, miA⟩ := regularity' (@singleton_ne_empty A),
  rw mem_singleton at mA, subst mA,
  apply mem_empty m, rw [←miA, mem_inter, mem_singleton], exact ⟨AA, rfl⟩,
end

-- Theorem 7X(b)
theorem no_2_cyle {a b : Set} : ¬ (a ∈ b ∧ b ∈ a) :=
begin
  rintro ⟨ab, ba⟩,
  have abne : ({a, b} : Set) ≠ ∅, apply ne_empty_of_inhabited, use a, rw [mem_insert], left, refl,
  obtain ⟨m, mab, miab⟩ := regularity' abne,
  rw [mem_insert, mem_singleton] at mab, cases mab with ma mb,
    subst ma, apply mem_empty b, rw [←miab, mem_inter, mem_insert, mem_singleton],
    exact ⟨ba, or.inr rfl⟩,
  subst mb, apply mem_empty a, rw [←miab, mem_inter, mem_insert],
  exact ⟨ab, or.inl rfl⟩,
end

-- Theorem 7X(c)
theorem no_ω_cycle : ¬ ∃ f : Set, f.is_function ∧ f.dom = ω ∧ ∀ {n : Set}, n ∈ ω → f.fun_value n.succ ∈ f.fun_value n :=
begin
  rintro ⟨f, ffun, fdom, fspec⟩,
  have ranne : f.ran ≠ ∅, apply ne_empty_of_inhabited, use f.fun_value ∅,
    apply fun_value_def'' ffun, rw fdom, exact zero_nat,
  obtain ⟨m, mf, mif⟩ := regularity' ranne,
  rw mem_ran_iff ffun at mf, rcases mf with ⟨n, nω, mn⟩, subst mn,
  apply mem_empty (f.fun_value n.succ), rw [←mif, mem_inter, mem_ran_iff ffun],
  rw fdom at nω, refine ⟨fspec nω, _, _, rfl⟩,
  rw fdom, exact nat_induct.succ_closed nω,
end

lemma rank_le_of_subset {x : Set} (xgr : x.grounded) {y : Set} (ygr : y.grounded) (xy : x ⊆ y) : x.rank ≤ y.rank :=
rank_least_of_grounded xgr (rank_ord_of_grounded ygr) (subset_trans xy (rank_sub_of_grounded ygr))

-- exercise 30(b)
theorem ch7_p30b {a : Set} : a.powerset.rank = a.rank.succ :=
begin
  rw rank_eq_of_all_mem_grounded (λ x h, all_grounded),
  apply ext, simp only [mem_Union, exists_prop, mem_repl_img, mem_powerset], intro z, split,
    rintro ⟨w, ⟨x, xa, wx⟩, zw⟩, subst wx, rw mem_succ_iff_le,
    have zord : z.is_ordinal := ord_of_mem_ord (succ_ord_of_ord (rank_ord_of_grounded all_grounded)) zw,
    rw ←rank_ord_eq_self zord at *, rw mem_succ_iff_le at zw,
    apply ord_le_trans (rank_ord_of_grounded all_grounded) zw,
    exact rank_le_of_subset all_grounded all_grounded xa,
  intro za, exact ⟨_, ⟨_, subset_self, rfl⟩, za⟩,
end

-- exercise 30(c)
theorem ch7_p30c {a : Set} : a.Union.rank ≤ a.rank :=
begin
  apply rank_least_of_grounded all_grounded (rank_ord_of_grounded all_grounded),
  simp only [subset_def, mem_Union, exists_prop], rintro z ⟨x, xa, zx⟩,
  suffices xa₂ : x.rank.Veb ⊆ a.rank.Veb,
    apply xa₂, apply rank_sub_of_grounded all_grounded, exact zx,
  apply Veb_sub_of_mem (rank_ord_of_grounded all_grounded),
  exact rank_mem_of_mem_grounded all_grounded xa,
end

-- exercise 33
theorem ch7_p33 {D : Set} (Dt : D.transitive_set) {B : Set} (BD : ∀ {a : Set}, a ∈ D → a ⊆ B → a ∈ B) : D ⊆ B :=
begin
  suffices h : ∀ {α : Set}, α.is_ordinal → D ∩ α.Veb ⊆ B,
    obtain ⟨α, αord, Dα⟩ := @all_grounded D,
    rw ←inter_eq_of_sub Dα, exact h αord,
  apply @trans_ind_schema (λ α, D ∩ α.Veb ⊆ B), intros α αord ind x xDα,
  rw [mem_inter, mem_Veb αord] at xDα, rcases xDα with ⟨xD, β, βα, xβ⟩,
  rw transitive_set_iff' at Dt, apply BD xD,
  exact subset_trans (sub_inter_of_sub (Dt xD) xβ) (ind βα),
end

-- exercise 35
theorem succ_inj' {a b : Set} (ab : a.succ = b.succ) : a = b :=
begin
  have amb : a ∈ b.succ, rw ←ab, exact self_mem_succ,
  have bma : b ∈ a.succ, rw ab, exact self_mem_succ,
  rw [succ, mem_union, mem_singleton] at amb bma,
  cases bma,
    symmetry, exact bma,
  cases amb,
    exact amb,
  exfalso, exact no_2_cyle ⟨bma, amb⟩,
end

theorem self_ne_succ {x : Set} : x.succ ≠ x :=
begin
  intro xx, apply @not_mem_self x, nth_rewrite 1 ←xx, exact self_mem_succ,
end

lemma eq_iff_le_and_le {a b : Set} : a = b ↔ a ≤ b ∧ b ≤ a :=
begin
  split,
    intro ab, subst ab, exact ⟨or.inr rfl, or.inr rfl⟩,
  rintro ⟨ab|ab, ba|ba⟩,
        exfalso, exact no_2_cyle ⟨ab, ba⟩,
      exact ba.symm,
    exact ab,
  exact ab,
end

-- exercise 38
theorem limit_ord_eq_Union {γ : Set} (γord : γ.limit_ord) : γ = γ.Union :=
begin
  rw eq_iff_subset_and_subset, split,
    intros α αγ, rw mem_Union,
    have αγ' : α.succ ∈ γ, apply classical.by_contradiction, intro αγ', apply γord.ns,
      use α, rw eq_iff_le_and_le,
      rw ord_not_lt_iff_le (succ_ord_of_ord (ord_of_mem_ord γord.ord αγ)) γord.ord at αγ',
      exact ⟨αγ', succ_least_upper_bound γord.ord αγ⟩,
    exact ⟨_, αγ', self_mem_succ⟩,
  exact (ordinal_trans γord.ord),
end

theorem zero_ne_succ_ord {α : Set} : ∅ ≠ α.succ :=
λ h, mem_empty α (by rw h; exact self_mem_succ)

theorem zero_mem_succ_ord {α : Set} (αord : α.is_ordinal) : ∅ ∈ α.succ :=
begin
  apply classical.by_contradiction, intro zα,
  rw ord_not_lt_iff_le zero_is_ord (succ_ord_of_ord αord) at zα, cases zα,
    exact mem_empty _ zα,
  exact zero_ne_succ_ord zα.symm,
end

theorem succ_ord_not_le_self {α : Set} (αord : α.is_ordinal) : ¬ (α.succ ≤ α) :=
λ αα, ord_mem_irrefl αord (ord_lt_of_lt_of_le αord self_mem_succ αα)

theorem ord_lt_of_succ_le {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal)
  (h : α.succ ≤ β) : α ∈ β :=
begin
  apply classical.by_contradiction, intro αβ,
  rw ord_not_lt_iff_le αord βord at αβ, exact succ_ord_not_le_self αord (ord_le_trans αord h αβ),
end

theorem ord_pos_of_inhab : ∀ {α : Set}, α.is_ordinal → α.inhab → ∅ ∈ α :=
begin
  apply @trans_ind_schema (λ α, α.inhab → ∅ ∈ α),
  rintros α αord ind ⟨β, βα⟩,
  by_cases hβ : β.inhab,
    exact ord_mem_trans αord (ind βα hβ) βα,
  have βz : β = ∅, rw eq_empty, intros δ δβ, exact hβ ⟨_, δβ⟩,
  subst βz, exact βα,
end

theorem ord_succ_lt_iff : ∀ {α : Set}, α.is_ordinal → ∀ {β : Set}, β.is_ordinal →
  (α ∈ β ↔ α.succ ∈ β.succ) :=
have h : ∀ {α β : Set}, β.is_ordinal → α ∈ β → α.succ ∈ β.succ,
  from λ α β βord αβ, ord_lt_of_le_of_lt (succ_ord_of_ord βord) (succ_least_upper_bound βord αβ) self_mem_succ,
λ α αord β βord,
⟨h βord, λ αβ, classical.by_contradiction (λ βα, begin
  rw ord_not_lt_iff_le αord βord at βα, cases βα,
    exact ord_mem_irrefl (succ_ord_of_ord βord) (ord_mem_trans (succ_ord_of_ord βord) (h αord βα) αβ),
  subst βα, exact ord_mem_irrefl (succ_ord_of_ord βord) αβ,
end)⟩

theorem ord_succ_inj {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal)
  (sαβ : α.succ = β.succ) : α = β :=
begin
  apply classical.by_contradiction, intro ne,
  cases ord_conn αord βord ne with αβ βα,
    rw ord_succ_lt_iff αord βord at αβ, rw sαβ at αβ,
    exact ord_mem_irrefl (succ_ord_of_ord βord) αβ,
  rw ord_succ_lt_iff βord αord at βα, rw sαβ at βα,
  exact ord_mem_irrefl (succ_ord_of_ord βord) βα,
end

theorem ord_succ_le_iff {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal) :
  α ≤ β ↔ α.succ ≤ β.succ :=
⟨λ αβ, αβ.elim (λ h, by left; rwa ←ord_succ_lt_iff αord βord) (λ h, by right; rw h),
λ αβ, αβ.elim (λ h, by left; rwa ord_succ_lt_iff αord βord) (λ h, or.inr (ord_succ_inj αord βord h))⟩

theorem empty_le_ord {α : Set} (αord : α.is_ordinal) : ∅ ≤ α :=
(ord_le_iff_sub zero_is_ord αord).mpr empty_subset

theorem limit_ord_inhab {γ : Set} (γord : γ.limit_ord) : γ.inhab :=
inhab_of_inf (limit_ord_inf γord)

theorem limit_ord_pos {γ : Set} (γord : γ.limit_ord) : ∅ ∈ γ :=
ord_pos_of_inhab γord.ord (limit_ord_inhab γord)

theorem ord_eq_zero_of_le_zero {α : Set} (αord : α.is_ordinal) (hα : α ≤ ∅) : α = ∅ :=
or.elim hα (λ h, false.elim (mem_empty _ h)) (λ h, h)

theorem not_zero_of_pos {α : Set} (hα : ∅ ∈ α) : α ≠ ∅ :=
ne_empty_of_inhabited _ ⟨_, hα⟩

lemma ord_cases {α : Set} (αord : α.is_ordinal) : α = ∅ ∨ (∃ β : Set, α = β.succ) ∨ α.limit_ord :=
classical.by_cases (λ αz : α = ∅, or.inl αz) (λ αnz, or.inr (
  classical.by_cases (λ ex : ∃ β : Set, α = β.succ, or.inl ex) (λ nex, or.inr ⟨αord, αnz, nex⟩)))

lemma card_is_card {α : Set} : α.card.is_cardinal :=
⟨_, rfl⟩

lemma card_pos_of_inhab {A : Set} (Ain : A.inhab) : ∅ ∈ A.card :=
begin
  cases @empty_le_ord A.card (card_is_ord card_is_card),
    exact h,
  exfalso, exact @ne_empty_of_inhabited _ Ain (eq_empty_of_card_empty h.symm),
end

lemma card_ge_one_of_inhab {A : Set} (Ain : A.inhab) : one ≤ A.card :=
succ_least_upper_bound (card_is_ord card_is_card) (card_pos_of_inhab Ain)

lemma ne_of_mem {A B : Set} (AB : A ∈ B) : A ≠ B :=
begin
  intro h, rw h at AB, apply not_mem_self AB,
end

lemma not_succ_le_empty {α : Set} : ¬ α.succ ≤ ∅ :=
λ h, or.elim h (λ h', mem_empty _ h') (λ h', zero_ne_succ_ord h'.symm)

lemma card_succ_eq {A : Set} : A.succ.card = A.card.card_add one :=
begin
  have h : A ∩ {A} = ∅, rw eq_empty, intros z hz, rw [mem_inter, mem_singleton] at hz,
    rcases hz with ⟨zA, zA'⟩, subst zA', exact not_mem_self zA,
  rw [succ, union_comm, card_add_spec rfl rfl h, card_singleton],
end

lemma succ_imm (m : Set) : ¬ ∃ k : Set, m ∈ k ∧ k ∈ m.succ :=
begin
  rintro ⟨k, mk, km⟩, rw [succ, mem_union, mem_singleton] at km, cases km,
    subst km, exact not_mem_self mk,
  exact no_2_cyle ⟨mk, km⟩,
end

lemma card_le_conn {κ : Set} (κcard : κ.is_cardinal) {μ : Set} (μcard : μ.is_cardinal) : κ.card_le μ ∨ μ.card_le κ :=
begin
  rcases κcard with ⟨K, Kcard⟩, rcases μcard with ⟨M, Mcard⟩,
  subst Kcard, subst Mcard, simp only [card_le_iff_equin'],
  cases ax_ch_5 K M with KM MK,
    left, exact KM,
  right, exact MK,
end

lemma card_not_lt_iff_le {κ : Set} (κcard : κ.is_cardinal) {μ : Set} (μcard : μ.is_cardinal) :
  ¬ κ.card_lt μ ↔ μ.card_le κ :=
begin
  split,
    intro κμ, rcases card_le_conn κcard μcard with (κμ'|μκ),
      rw card_le_iff at κμ', cases κμ',
        exfalso, exact κμ κμ',
      subst κμ', rw card_le_iff, right, refl,
    exact μκ,
  intros μκ κμ, rw card_le_iff at μκ, cases μκ,
    exact not_card_lt_cycle κcard μcard ⟨κμ, μκ⟩,
  subst μκ, exact κμ.right rfl,
end

lemma card_not_le_iff_lt {κ : Set} (κcard : κ.is_cardinal) {μ : Set} (μcard : μ.is_cardinal) :
  ¬ κ.card_le μ ↔ μ.card_lt κ :=
by simp only [←card_not_lt_iff_le μcard κcard, not_not]

lemma card_le_of_ord_mem {α : Set} (αord : α.is_ordinal) {β : Set} (βα : β ∈ α) : β.card.card_le α.card :=
begin
  have βord := ord_of_mem_ord αord βα,
  rw ord_mem_iff_ssub βord αord at βα, exact card_le_of_subset βα.left,
end

lemma card_lt_iff_ord_mem {α : Set} (αord : α.is_ordinal) {β : Set} (βord : β.is_ordinal)
  (h : α.card.card_lt β.card) : α ∈ β :=
begin
  rcases h with ⟨le, ne⟩, rw ←ord_not_le_iff_lt βord αord, rintro (h|h),
    exact ne (card_eq_of_le_of_le card_is_card card_is_card le (card_le_of_ord_mem αord h)),
  subst h, exact ne rfl,
end

lemma card_le_of_ord_le {α : Set} (αord : α.is_ordinal) {β : Set} (βα : β ≤ α) : β.card.card_le α.card :=
begin
  cases βα,
    exact card_le_of_ord_mem αord βα,
  subst βα, exact card_le_refl,
end

lemma card_mul_lt_of_lt_of_lt {ν : Set} (hν : ν.is_cardinal) {κ : Set} (hκ : κ.is_cardinal) (κν : κ.card_lt ν)
  {μ : Set} (hμ : μ.is_cardinal) (μν : μ.card_lt ν) : (κ.card_mul μ).card_lt (ν.card_mul ν) :=
begin
  cases card_le_conn hκ hμ with κμ μκ,
    apply card_lt_of_le_of_lt (mul_cardinal hκ hμ) (mul_cardinal hμ hμ) (card_mul_le_of_le_left hκ hμ κμ hμ),
    exact card_mul_lt_mul hμ hν μν,
  apply card_lt_of_le_of_lt (mul_cardinal hκ hμ) (mul_cardinal hκ hκ) (card_mul_le_of_le_right hμ hκ μκ hκ),
  exact card_mul_lt_mul hκ hν κν,
end

end Set