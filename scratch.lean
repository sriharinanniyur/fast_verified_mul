import Mathlib

lemma transitive_property (P : Prop) (Q : Prop) (R : Prop) :
  ((P → Q) ∧ (Q → R)) → (P → R) := by
  tauto
