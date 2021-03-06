import data.list
import tactic

universes u v w

theorem list.tfae_prf {a b : Prop} {l : list Prop} (h : list.tfae l) (ha : a ∈ l) (hb : b ∈ l) (ha_prf : a) : b :=
(h a ha b hb).mp ha_prf

lemma and_iff_right_of_left_if_right {p q : Prop} (h : p → q) : q ∧ p ↔ p :=
⟨λ h₂, h₂.right, λ h₂, ⟨h h₂, h₂⟩⟩

lemma choice_2_arg {α : Sort u} {β : Sort v} {γ : α → β → Sort w}
{r : Π (x : α) (y : β), γ x y → Prop} (h : ∀ (x : α) (y : β), ∃ (z : γ x y), r x y z) :
∃ (f : Π (x : α) (y : β), γ x y), ∀ (x : α) (y : β), r x y (f x y) :=
begin
  let γ' : (pprod α β) → Sort w := (λ z, γ z.fst z.snd),
  let r' := λ (x : pprod α β) (z : γ' x), r x.fst x.snd z,
  have h' : ∀ (x : pprod α β), ∃ z : γ' x, r' x z := (λ x, h x.fst x.snd),
  rcases classical.axiom_of_choice h' with ⟨f, hf⟩,
  let f := (λ x y, f ⟨x, y⟩),
  existsi f, intros x y, exact hf ⟨x, y⟩,
end

lemma subst_right_of_and {α : Sort u} {p : Prop} {a b c : α} (h : p → b = c) : p ∧ a = b ↔ p ∧ a = c :=
⟨ assume h₂, ⟨h₂.left, (h h₂.left) ▸ h₂.right⟩,
  assume h₂, ⟨h₂.left, (h h₂.left).symm ▸ h₂.right⟩ ⟩

lemma exists_unique_eq {α : Sort u} {β : Sort v} (f : α → β) : ∀ x : α, ∃! y : β, (λ (a : α) (b : β), b = f a) x y :=
λ x, ⟨f x, rfl, λ y, assume hy, hy⟩

lemma rel_congr_left {α : Sort u} {r : α → α → Prop} (symm : symmetric r) (trans : transitive r)
  {x y : α} (xy : r x y) {z : α} : r x z ↔ r y z :=
⟨λ xz, trans (symm xy) xz, λ yz, trans xy yz⟩

lemma iff_of_not_of_not {p : Prop} (np : ¬ p) {q : Prop} (nq : ¬ q) : p ↔ q :=
⟨λ hp, false.elim (np hp), λ hq, false.elim (nq hq)⟩

lemma ite_prop {α : Sort u} {p : α → Prop} {x y : α} (px : p x) (py : p y) {q : Prop} [h : decidable q] :
p (if q then x else y) :=
begin
  by_cases q,
    rw if_pos h, exact px,
  rw if_neg h, exact py,
end