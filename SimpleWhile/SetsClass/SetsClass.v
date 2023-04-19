Require Export SetsClass.SetElement.
Require Export SetsClass.SetsDomain.
Require Export SetsClass.RelsDomain.

Module SetsNotation.

Declare Scope sets_scope.
Delimit Scope sets_scope with sets.

Notation "[ ]":= Sets.empty (format "[ ]"): sets_scope.
Notation "∅":= Sets.empty (at level 5, no associativity): sets_scope.
Notation "[ x ]":= (Sets.singleton x) : sets_scope.
Notation "x ∩ y" := (Sets.intersect x y)(at level 11, left associativity): sets_scope.
Notation "x ∪ y" := (Sets.union x y)(at level 12, left associativity): sets_scope.
Notation "⋃ x" := (Sets.indexed_union x)(at level 10, no associativity): sets_scope.
Notation "⋂ x" := (Sets.indexed_intersect x)(at level 10, no associativity): sets_scope.
Notation "x == y" := (Sets.equiv x y) (at level 70, no associativity): sets_scope.
Notation "x ⊆ y" := (Sets.included x y) (at level 70, no associativity): sets_scope.
Notation "x ∈ y" := (SetsEle.In x y) (at level 70, no associativity): sets_scope.
Notation "⌜ x ⌝" := (Sets.prop_inj x) (at level 40, no associativity): sets_scope.
Notation "X ∘ Y" := (Rels.concat X Y) (right associativity, at level 60): sets_scope.

End SetsNotation.
