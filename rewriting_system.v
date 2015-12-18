Require Import Relations.



Module Type REWRITING_SYSTEM.

  Parameters
  (configuration : Set)
  (transition    : configuration -> configuration -> Prop).

  Notation "c1 → c2"  := (transition c1 c2)              (no associativity, at level 70).
  Notation "t1 →+ t2" := (clos_trans_1n _ transition t1 t2) 
                                                         (no associativity, at level 70).
  Notation "t1 →* t2" := (clos_refl_trans_1n _ transition t1 t2) 
                                                         (no associativity, at level 70).

End REWRITING_SYSTEM.